import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H3.R1
-- Upstream path: reductions/Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H3.R1.lean
-- Credit: @adammcarter (agent: Claude Code, model claude-fable-5-2)
--
-- Splits step H3 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1 (the unitary perfect number n has
-- exactly one repeated odd prime z, exponent e = v_z(n) = 4 mod 8, z one of 11, 419, 463, 503, 607, 883,
-- 1019, 1327, a = padicValNat 2 n).  Proving H1 and H2 proves the step.
--
-- Notation as in the parent file: P = the set of simple odd primes of n.  The balance equation is
--   (2^a + 1)(1 + z^e) prod_P (p + 1) = 2^(a+1) z^e prod_P p,
-- in which every odd prime other than z occurs exactly once on the left.  If e is an odd multiple of d
-- then z^d + 1 divides 1 + z^e; its odd primes are simple primes of n, and the odd primes (other than z)
-- of p + 1 for simple p are simple again.
--
-- PROVED BELOW (no hypothesis needed):
--  * z = 419, 463, 503, 607, 883, 1019, 1327 are impossible (theorems k4_<z>): the forced chain from
--    z^4 + 1 ends in a square dividing some p + 1 or in a prime with two sources on the left.
--    So z = 11.
--  * z = 11: no prime k in the list K below divides e (theorems k11_<k>, esieve11).  If k divides e
--    then e is an odd multiple of 4k, and the forced chain from a prime of 11^(4k) + 1 ends in a
--    contradiction of the same two kinds.  K = 58 odd primes below 400; the odd primes below 400 not in K
--    are 113, 149, 211, 229, 251, 257, 263, 277, 311, 313, 317, 331, 347, 349, 353, 379, 383, 389, 397
--    (no usable prime factor of 11^(4k) + 1 was found for them).  So e = 4, or e >= 452.
--  The comment above each k4_<z>, k11_<k> names the contradiction.  Primes above 4.3 * 10^7 on the
--  chains carry a Lucas certificate (theorems prime_<p>, 43 new, up to 50 digits).
--
-- H1 (OPEN): z = 11 and e = 4.  Here 11^4 + 1 = 2 * 7321 and the forced simple primes are
--   7321, 523, 131, 7, 3, with no contradiction among them.
-- H2 (OPEN): z = 11, e = 4 mod 8, e > 4, no prime of K divides e.
-- Each H keeps the conditions of the parent step on a that are not vacuous for z = 11.
-- No known unitary perfect number has a repeated odd prime z >= 7.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H3_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1 hiding H1 H2 H3 H4 main

-- H1: a is bounded when z = 11 and e = 4.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 11) →
    n.factorization 11 = 4 →
    padicValNat 2 n % 6 ≠ 3 → padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n % 8 ≠ 4 → padicValNat 2 n % 4096 ≠ 2048 →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ 11 ∣ 2 ^ d + 1) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- H2: a is bounded when z = 11, e = 4 mod 8, e > 4 and no prime of the list divides e.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 11) →
    n.factorization 11 % 8 = 4 → 4 < n.factorization 11 →
    (∀ k ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
      101, 103, 107, 109, 127, 131, 137, 139, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197,
      199, 223, 227, 233, 239, 241, 269, 271, 281, 283, 293, 307, 337, 359, 367, 373} : Finset ℕ),
      ¬ k ∣ n.factorization 11) →
    padicValNat 2 n % 6 ≠ 3 → padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n % 8 ≠ 4 → padicValNat 2 n % 4096 ≠ 2048 →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ 11 ∣ 2 ^ d + 1) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- Section 1. Certificates and the chains.

theorem prime_15410832361 : Nat.Prime 15410832361 := by
  refine lucas_primality 15410832361 (13 : ZMod 15410832361) ?_ (fun q hq hd => ?_)
  · rw [show 15410832361 - 1 = 15410832360 from by norm_num]
    reduce_mod_char
  · have e : 15410832361 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 19 ^ 1, 41 ^ 1, 2141 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15410832361 - 1) / 2 = 7705416180 from by norm_num]
      have h2 : (13 : ZMod 15410832361) ^ 7705416180 = ((15410832360 : ℕ) : ZMod 15410832361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15410832361 - 1) / 3 = 5136944120 from by norm_num]
      have h2 : (13 : ZMod 15410832361) ^ 5136944120 = ((12441415479 : ℕ) : ZMod 15410832361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15410832361 - 1) / 5 = 3082166472 from by norm_num]
      have h2 : (13 : ZMod 15410832361) ^ 3082166472 = ((5424294984 : ℕ) : ZMod 15410832361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15410832361 - 1) / 7 = 2201547480 from by norm_num]
      have h2 : (13 : ZMod 15410832361) ^ 2201547480 = ((12838606206 : ℕ) : ZMod 15410832361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15410832361 - 1) / 11 = 1400984760 from by norm_num]
      have h2 : (13 : ZMod 15410832361) ^ 1400984760 = ((14013031266 : ℕ) : ZMod 15410832361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15410832361 - 1) / 19 = 811096440 from by norm_num]
      have h2 : (13 : ZMod 15410832361) ^ 811096440 = ((7616753414 : ℕ) : ZMod 15410832361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15410832361 - 1) / 41 = 375873960 from by norm_num]
      have h2 : (13 : ZMod 15410832361) ^ 375873960 = ((13759124612 : ℕ) : ZMod 15410832361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15410832361 - 1) / 2141 = 7197960 from by norm_num]
      have h2 : (13 : ZMod 15410832361) ^ 7197960 = ((14711499842 : ℕ) : ZMod 15410832361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7705416181 : Nat.Prime 7705416181 := by
  refine lucas_primality 7705416181 (24 : ZMod 7705416181) ?_ (fun q hq hd => ?_)
  · rw [show 7705416181 - 1 = 7705416180 from by norm_num]
    reduce_mod_char
  · have e : 7705416181 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 19 ^ 1, 41 ^ 1, 2141 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7705416181 - 1) / 2 = 3852708090 from by norm_num]
      have h2 : (24 : ZMod 7705416181) ^ 3852708090 = ((7705416180 : ℕ) : ZMod 7705416181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7705416181 - 1) / 3 = 2568472060 from by norm_num]
      have h2 : (24 : ZMod 7705416181) ^ 2568472060 = ((87780 : ℕ) : ZMod 7705416181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7705416181 - 1) / 5 = 1541083236 from by norm_num]
      have h2 : (24 : ZMod 7705416181) ^ 1541083236 = ((166998730 : ℕ) : ZMod 7705416181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7705416181 - 1) / 7 = 1100773740 from by norm_num]
      have h2 : (24 : ZMod 7705416181) ^ 1100773740 = ((3725832853 : ℕ) : ZMod 7705416181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7705416181 - 1) / 11 = 700492380 from by norm_num]
      have h2 : (24 : ZMod 7705416181) ^ 700492380 = ((3493703586 : ℕ) : ZMod 7705416181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7705416181 - 1) / 19 = 405548220 from by norm_num]
      have h2 : (24 : ZMod 7705416181) ^ 405548220 = ((3194876752 : ℕ) : ZMod 7705416181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7705416181 - 1) / 41 = 187936980 from by norm_num]
      have h2 : (24 : ZMod 7705416181) ^ 187936980 = ((2108050972 : ℕ) : ZMod 7705416181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7705416181 - 1) / 2141 = 3598980 from by norm_num]
      have h2 : (24 : ZMod 7705416181) ^ 3598980 = ((3760403918 : ℕ) : ZMod 7705416181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3852708091 : Nat.Prime 3852708091 := by
  refine lucas_primality 3852708091 (7 : ZMod 3852708091) ?_ (fun q hq hd => ?_)
  · rw [show 3852708091 - 1 = 3852708090 from by norm_num]
    reduce_mod_char
  · have e : 3852708091 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 19 ^ 1, 41 ^ 1, 2141 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3852708091 - 1) / 2 = 1926354045 from by norm_num]
      have h2 : (7 : ZMod 3852708091) ^ 1926354045 = ((3852708090 : ℕ) : ZMod 3852708091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3852708091 - 1) / 3 = 1284236030 from by norm_num]
      have h2 : (7 : ZMod 3852708091) ^ 1284236030 = ((2462519528 : ℕ) : ZMod 3852708091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3852708091 - 1) / 5 = 770541618 from by norm_num]
      have h2 : (7 : ZMod 3852708091) ^ 770541618 = ((1269684938 : ℕ) : ZMod 3852708091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3852708091 - 1) / 7 = 550386870 from by norm_num]
      have h2 : (7 : ZMod 3852708091) ^ 550386870 = ((2572774818 : ℕ) : ZMod 3852708091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3852708091 - 1) / 11 = 350246190 from by norm_num]
      have h2 : (7 : ZMod 3852708091) ^ 350246190 = ((1371194461 : ℕ) : ZMod 3852708091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3852708091 - 1) / 19 = 202774110 from by norm_num]
      have h2 : (7 : ZMod 3852708091) ^ 202774110 = ((390710963 : ℕ) : ZMod 3852708091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3852708091 - 1) / 41 = 93968490 from by norm_num]
      have h2 : (7 : ZMod 3852708091) ^ 93968490 = ((2982185327 : ℕ) : ZMod 3852708091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3852708091 - 1) / 2141 = 1799490 from by norm_num]
      have h2 : (7 : ZMod 3852708091) ^ 1799490 = ((1440405814 : ℕ) : ZMod 3852708091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_22977034081 : Nat.Prime 22977034081 := by
  refine lucas_primality 22977034081 (31 : ZMod 22977034081) ?_ (fun q hq hd => ?_)
  · rw [show 22977034081 - 1 = 22977034080 from by norm_num]
    reduce_mod_char
  · have e : 22977034081 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 13 ^ 1, 17 ^ 1, 29 ^ 1, 97 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22977034081 - 1) / 2 = 11488517040 from by norm_num]
      have h2 : (31 : ZMod 22977034081) ^ 11488517040 = ((22977034080 : ℕ) : ZMod 22977034081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22977034081 - 1) / 3 = 7659011360 from by norm_num]
      have h2 : (31 : ZMod 22977034081) ^ 7659011360 = ((12558155678 : ℕ) : ZMod 22977034081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22977034081 - 1) / 5 = 4595406816 from by norm_num]
      have h2 : (31 : ZMod 22977034081) ^ 4595406816 = ((22511439771 : ℕ) : ZMod 22977034081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22977034081 - 1) / 7 = 3282433440 from by norm_num]
      have h2 : (31 : ZMod 22977034081) ^ 3282433440 = ((16267649650 : ℕ) : ZMod 22977034081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22977034081 - 1) / 11 = 2088821280 from by norm_num]
      have h2 : (31 : ZMod 22977034081) ^ 2088821280 = ((8241327657 : ℕ) : ZMod 22977034081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22977034081 - 1) / 13 = 1767464160 from by norm_num]
      have h2 : (31 : ZMod 22977034081) ^ 1767464160 = ((21231227838 : ℕ) : ZMod 22977034081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22977034081 - 1) / 17 = 1351590240 from by norm_num]
      have h2 : (31 : ZMod 22977034081) ^ 1351590240 = ((18846239813 : ℕ) : ZMod 22977034081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22977034081 - 1) / 29 = 792311520 from by norm_num]
      have h2 : (31 : ZMod 22977034081) ^ 792311520 = ((18237941403 : ℕ) : ZMod 22977034081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22977034081 - 1) / 97 = 236876640 from by norm_num]
      have h2 : (31 : ZMod 22977034081) ^ 236876640 = ((1290976521 : ℕ) : ZMod 22977034081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11488517041 : Nat.Prime 11488517041 := by
  refine lucas_primality 11488517041 (38 : ZMod 11488517041) ?_ (fun q hq hd => ?_)
  · rw [show 11488517041 - 1 = 11488517040 from by norm_num]
    reduce_mod_char
  · have e : 11488517041 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 13 ^ 1, 17 ^ 1, 29 ^ 1, 97 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11488517041 - 1) / 2 = 5744258520 from by norm_num]
      have h2 : (38 : ZMod 11488517041) ^ 5744258520 = ((11488517040 : ℕ) : ZMod 11488517041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11488517041 - 1) / 3 = 3829505680 from by norm_num]
      have h2 : (38 : ZMod 11488517041) ^ 3829505680 = ((11488409856 : ℕ) : ZMod 11488517041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11488517041 - 1) / 5 = 2297703408 from by norm_num]
      have h2 : (38 : ZMod 11488517041) ^ 2297703408 = ((3941837015 : ℕ) : ZMod 11488517041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11488517041 - 1) / 7 = 1641216720 from by norm_num]
      have h2 : (38 : ZMod 11488517041) ^ 1641216720 = ((2753534544 : ℕ) : ZMod 11488517041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11488517041 - 1) / 11 = 1044410640 from by norm_num]
      have h2 : (38 : ZMod 11488517041) ^ 1044410640 = ((8286430870 : ℕ) : ZMod 11488517041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11488517041 - 1) / 13 = 883732080 from by norm_num]
      have h2 : (38 : ZMod 11488517041) ^ 883732080 = ((2788266954 : ℕ) : ZMod 11488517041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11488517041 - 1) / 17 = 675795120 from by norm_num]
      have h2 : (38 : ZMod 11488517041) ^ 675795120 = ((5202764330 : ℕ) : ZMod 11488517041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11488517041 - 1) / 29 = 396155760 from by norm_num]
      have h2 : (38 : ZMod 11488517041) ^ 396155760 = ((4981918674 : ℕ) : ZMod 11488517041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11488517041 - 1) / 97 = 118438320 from by norm_num]
      have h2 : (38 : ZMod 11488517041) ^ 118438320 = ((4651390497 : ℕ) : ZMod 11488517041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_32006777041 : Nat.Prime 32006777041 := by
  refine lucas_primality 32006777041 (11 : ZMod 32006777041) ?_ (fun q hq hd => ?_)
  · rw [show 32006777041 - 1 = 32006777040 from by norm_num]
    reduce_mod_char
  · have e : 32006777041 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 1, 7 ^ 1, 251 ^ 1, 25301 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32006777041 - 1) / 2 = 16003388520 from by norm_num]
      have h2 : (11 : ZMod 32006777041) ^ 16003388520 = ((32006777040 : ℕ) : ZMod 32006777041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32006777041 - 1) / 3 = 10668925680 from by norm_num]
      have h2 : (11 : ZMod 32006777041) ^ 10668925680 = ((25568224129 : ℕ) : ZMod 32006777041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32006777041 - 1) / 5 = 6401355408 from by norm_num]
      have h2 : (11 : ZMod 32006777041) ^ 6401355408 = ((3855996551 : ℕ) : ZMod 32006777041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32006777041 - 1) / 7 = 4572396720 from by norm_num]
      have h2 : (11 : ZMod 32006777041) ^ 4572396720 = ((28269152640 : ℕ) : ZMod 32006777041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32006777041 - 1) / 251 = 127517040 from by norm_num]
      have h2 : (11 : ZMod 32006777041) ^ 127517040 = ((8448706644 : ℕ) : ZMod 32006777041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32006777041 - 1) / 25301 = 1265040 from by norm_num]
      have h2 : (11 : ZMod 32006777041) ^ 1265040 = ((17202082753 : ℕ) : ZMod 32006777041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_16003388521 : Nat.Prime 16003388521 := by
  refine lucas_primality 16003388521 (11 : ZMod 16003388521) ?_ (fun q hq hd => ?_)
  · rw [show 16003388521 - 1 = 16003388520 from by norm_num]
    reduce_mod_char
  · have e : 16003388521 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 7 ^ 1, 251 ^ 1, 25301 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16003388521 - 1) / 2 = 8001694260 from by norm_num]
      have h2 : (11 : ZMod 16003388521) ^ 8001694260 = ((16003388520 : ℕ) : ZMod 16003388521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16003388521 - 1) / 3 = 5334462840 from by norm_num]
      have h2 : (11 : ZMod 16003388521) ^ 5334462840 = ((126504 : ℕ) : ZMod 16003388521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16003388521 - 1) / 5 = 3200677704 from by norm_num]
      have h2 : (11 : ZMod 16003388521) ^ 3200677704 = ((11083751796 : ℕ) : ZMod 16003388521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16003388521 - 1) / 7 = 2286198360 from by norm_num]
      have h2 : (11 : ZMod 16003388521) ^ 2286198360 = ((1206101225 : ℕ) : ZMod 16003388521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16003388521 - 1) / 251 = 63758520 from by norm_num]
      have h2 : (11 : ZMod 16003388521) ^ 63758520 = ((8767226493 : ℕ) : ZMod 16003388521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16003388521 - 1) / 25301 = 632520 from by norm_num]
      have h2 : (11 : ZMod 16003388521) ^ 632520 = ((3610731027 : ℕ) : ZMod 16003388521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_727426751 : Nat.Prime 727426751 := by
  refine lucas_primality 727426751 (7 : ZMod 727426751) ?_ (fun q hq hd => ?_)
  · rw [show 727426751 - 1 = 727426750 from by norm_num]
    reduce_mod_char
  · have e : 727426751 - 1 = [2 ^ 1, 5 ^ 3, 23 ^ 1, 73 ^ 1, 1733 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (727426751 - 1) / 2 = 363713375 from by norm_num]
      have h2 : (7 : ZMod 727426751) ^ 363713375 = ((727426750 : ℕ) : ZMod 727426751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (727426751 - 1) / 5 = 145485350 from by norm_num]
      have h2 : (7 : ZMod 727426751) ^ 145485350 = ((309193669 : ℕ) : ZMod 727426751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (727426751 - 1) / 23 = 31627250 from by norm_num]
      have h2 : (7 : ZMod 727426751) ^ 31627250 = ((448598816 : ℕ) : ZMod 727426751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (727426751 - 1) / 73 = 9964750 from by norm_num]
      have h2 : (7 : ZMod 727426751) ^ 9964750 = ((30989855 : ℕ) : ZMod 727426751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (727426751 - 1) / 1733 = 419750 from by norm_num]
      have h2 : (7 : ZMod 727426751) ^ 419750 = ((377485651 : ℕ) : ZMod 727426751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_67877332801 : Nat.Prime 67877332801 := by
  refine lucas_primality 67877332801 (14 : ZMod 67877332801) ?_ (fun q hq hd => ?_)
  · rw [show 67877332801 - 1 = 67877332800 from by norm_num]
    reduce_mod_char
  · have e : 67877332801 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 2, 19 ^ 1, 101 ^ 1, 7369 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67877332801 - 1) / 2 = 33938666400 from by norm_num]
      have h2 : (14 : ZMod 67877332801) ^ 33938666400 = ((67877332800 : ℕ) : ZMod 67877332801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67877332801 - 1) / 3 = 22625777600 from by norm_num]
      have h2 : (14 : ZMod 67877332801) ^ 22625777600 = ((5154346374 : ℕ) : ZMod 67877332801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67877332801 - 1) / 5 = 13575466560 from by norm_num]
      have h2 : (14 : ZMod 67877332801) ^ 13575466560 = ((5200596782 : ℕ) : ZMod 67877332801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67877332801 - 1) / 19 = 3572491200 from by norm_num]
      have h2 : (14 : ZMod 67877332801) ^ 3572491200 = ((59126839537 : ℕ) : ZMod 67877332801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67877332801 - 1) / 101 = 672052800 from by norm_num]
      have h2 : (14 : ZMod 67877332801) ^ 672052800 = ((52977531416 : ℕ) : ZMod 67877332801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67877332801 - 1) / 7369 = 9211200 from by norm_num]
      have h2 : (14 : ZMod 67877332801) ^ 9211200 = ((44595845053 : ℕ) : ZMod 67877332801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_33938666401 : Nat.Prime 33938666401 := by
  refine lucas_primality 33938666401 (29 : ZMod 33938666401) ?_ (fun q hq hd => ?_)
  · rw [show 33938666401 - 1 = 33938666400 from by norm_num]
    reduce_mod_char
  · have e : 33938666401 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 2, 19 ^ 1, 101 ^ 1, 7369 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33938666401 - 1) / 2 = 16969333200 from by norm_num]
      have h2 : (29 : ZMod 33938666401) ^ 16969333200 = ((33938666400 : ℕ) : ZMod 33938666401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33938666401 - 1) / 3 = 11312888800 from by norm_num]
      have h2 : (29 : ZMod 33938666401) ^ 11312888800 = ((184224 : ℕ) : ZMod 33938666401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33938666401 - 1) / 5 = 6787733280 from by norm_num]
      have h2 : (29 : ZMod 33938666401) ^ 6787733280 = ((24505937687 : ℕ) : ZMod 33938666401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33938666401 - 1) / 19 = 1786245600 from by norm_num]
      have h2 : (29 : ZMod 33938666401) ^ 1786245600 = ((30932155600 : ℕ) : ZMod 33938666401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33938666401 - 1) / 101 = 336026400 from by norm_num]
      have h2 : (29 : ZMod 33938666401) ^ 336026400 = ((21258035656 : ℕ) : ZMod 33938666401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33938666401 - 1) / 7369 = 4605600 from by norm_num]
      have h2 : (29 : ZMod 33938666401) ^ 4605600 = ((11991446752 : ℕ) : ZMod 33938666401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_16969333201 : Nat.Prime 16969333201 := by
  refine lucas_primality 16969333201 (13 : ZMod 16969333201) ?_ (fun q hq hd => ?_)
  · rw [show 16969333201 - 1 = 16969333200 from by norm_num]
    reduce_mod_char
  · have e : 16969333201 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 2, 19 ^ 1, 101 ^ 1, 7369 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16969333201 - 1) / 2 = 8484666600 from by norm_num]
      have h2 : (13 : ZMod 16969333201) ^ 8484666600 = ((16969333200 : ℕ) : ZMod 16969333201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16969333201 - 1) / 3 = 5656444400 from by norm_num]
      have h2 : (13 : ZMod 16969333201) ^ 5656444400 = ((14495545785 : ℕ) : ZMod 16969333201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16969333201 - 1) / 5 = 3393866640 from by norm_num]
      have h2 : (13 : ZMod 16969333201) ^ 3393866640 = ((8084709726 : ℕ) : ZMod 16969333201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16969333201 - 1) / 19 = 893122800 from by norm_num]
      have h2 : (13 : ZMod 16969333201) ^ 893122800 = ((9345325007 : ℕ) : ZMod 16969333201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16969333201 - 1) / 101 = 168013200 from by norm_num]
      have h2 : (13 : ZMod 16969333201) ^ 168013200 = ((327295462 : ℕ) : ZMod 16969333201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16969333201 - 1) / 7369 = 2302800 from by norm_num]
      have h2 : (13 : ZMod 16969333201) ^ 2302800 = ((13592236280 : ℕ) : ZMod 16969333201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_303957468361 : Nat.Prime 303957468361 := by
  refine lucas_primality 303957468361 (11 : ZMod 303957468361) ?_ (fun q hq hd => ?_)
  · rw [show 303957468361 - 1 = 303957468360 from by norm_num]
    reduce_mod_char
  · have e : 303957468361 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 7 ^ 2, 13 ^ 1, 17 ^ 1, 77969 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (303957468361 - 1) / 2 = 151978734180 from by norm_num]
      have h2 : (11 : ZMod 303957468361) ^ 151978734180 = ((303957468360 : ℕ) : ZMod 303957468361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (303957468361 - 1) / 3 = 101319156120 from by norm_num]
      have h2 : (11 : ZMod 303957468361) ^ 101319156120 = ((65236092664 : ℕ) : ZMod 303957468361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (303957468361 - 1) / 5 = 60791493672 from by norm_num]
      have h2 : (11 : ZMod 303957468361) ^ 60791493672 = ((97304001960 : ℕ) : ZMod 303957468361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (303957468361 - 1) / 7 = 43422495480 from by norm_num]
      have h2 : (11 : ZMod 303957468361) ^ 43422495480 = ((129621693467 : ℕ) : ZMod 303957468361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (303957468361 - 1) / 13 = 23381343720 from by norm_num]
      have h2 : (11 : ZMod 303957468361) ^ 23381343720 = ((228733935406 : ℕ) : ZMod 303957468361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (303957468361 - 1) / 17 = 17879851080 from by norm_num]
      have h2 : (11 : ZMod 303957468361) ^ 17879851080 = ((181577784497 : ℕ) : ZMod 303957468361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (303957468361 - 1) / 77969 = 3898440 from by norm_num]
      have h2 : (11 : ZMod 303957468361) ^ 3898440 = ((105608984411 : ℕ) : ZMod 303957468361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3534389167 : Nat.Prime 3534389167 := by
  refine lucas_primality 3534389167 (6 : ZMod 3534389167) ?_ (fun q hq hd => ?_)
  · rw [show 3534389167 - 1 = 3534389166 from by norm_num]
    reduce_mod_char
  · have e : 3534389167 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 11 ^ 1, 61 ^ 1, 83 ^ 1, 1511 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3534389167 - 1) / 2 = 1767194583 from by norm_num]
      have h2 : (6 : ZMod 3534389167) ^ 1767194583 = ((3534389166 : ℕ) : ZMod 3534389167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3534389167 - 1) / 3 = 1178129722 from by norm_num]
      have h2 : (6 : ZMod 3534389167) ^ 1178129722 = ((389844 : ℕ) : ZMod 3534389167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3534389167 - 1) / 7 = 504912738 from by norm_num]
      have h2 : (6 : ZMod 3534389167) ^ 504912738 = ((2918981957 : ℕ) : ZMod 3534389167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3534389167 - 1) / 11 = 321308106 from by norm_num]
      have h2 : (6 : ZMod 3534389167) ^ 321308106 = ((1902840550 : ℕ) : ZMod 3534389167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3534389167 - 1) / 61 = 57940806 from by norm_num]
      have h2 : (6 : ZMod 3534389167) ^ 57940806 = ((135656297 : ℕ) : ZMod 3534389167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3534389167 - 1) / 83 = 42583002 from by norm_num]
      have h2 : (6 : ZMod 3534389167) ^ 42583002 = ((226909821 : ℕ) : ZMod 3534389167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3534389167 - 1) / 1511 = 2339106 from by norm_num]
      have h2 : (6 : ZMod 3534389167) ^ 2339106 = ((3008252581 : ℕ) : ZMod 3534389167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_220899323 : Nat.Prime 220899323 := by
  refine lucas_primality 220899323 (2 : ZMod 220899323) ?_ (fun q hq hd => ?_)
  · rw [show 220899323 - 1 = 220899322 from by norm_num]
    reduce_mod_char
  · have e : 220899323 - 1 = [2 ^ 1, 7 ^ 1, 29 ^ 1, 101 ^ 1, 5387 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220899323 - 1) / 2 = 110449661 from by norm_num]
      have h2 : (2 : ZMod 220899323) ^ 110449661 = ((220899322 : ℕ) : ZMod 220899323) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220899323 - 1) / 7 = 31557046 from by norm_num]
      have h2 : (2 : ZMod 220899323) ^ 31557046 = ((152252801 : ℕ) : ZMod 220899323) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220899323 - 1) / 29 = 7617218 from by norm_num]
      have h2 : (2 : ZMod 220899323) ^ 7617218 = ((67620291 : ℕ) : ZMod 220899323) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220899323 - 1) / 101 = 2187122 from by norm_num]
      have h2 : (2 : ZMod 220899323) ^ 2187122 = ((64902007 : ℕ) : ZMod 220899323) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220899323 - 1) / 5387 = 41006 from by norm_num]
      have h2 : (2 : ZMod 220899323) ^ 41006 = ((2728000 : ℕ) : ZMod 220899323) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_539096783161 : Nat.Prime 539096783161 := by
  refine lucas_primality 539096783161 (7 : ZMod 539096783161) ?_ (fun q hq hd => ?_)
  · rw [show 539096783161 - 1 = 539096783160 from by norm_num]
    reduce_mod_char
  · have e : 539096783161 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 13 ^ 1, 17 ^ 1, 509 ^ 1, 39937 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (539096783161 - 1) / 2 = 269548391580 from by norm_num]
      have h2 : (7 : ZMod 539096783161) ^ 269548391580 = ((539096783160 : ℕ) : ZMod 539096783161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (539096783161 - 1) / 3 = 179698927720 from by norm_num]
      have h2 : (7 : ZMod 539096783161) ^ 179698927720 = ((74345827627 : ℕ) : ZMod 539096783161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (539096783161 - 1) / 5 = 107819356632 from by norm_num]
      have h2 : (7 : ZMod 539096783161) ^ 107819356632 = ((57074814385 : ℕ) : ZMod 539096783161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (539096783161 - 1) / 13 = 41468983320 from by norm_num]
      have h2 : (7 : ZMod 539096783161) ^ 41468983320 = ((425461639436 : ℕ) : ZMod 539096783161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (539096783161 - 1) / 17 = 31711575480 from by norm_num]
      have h2 : (7 : ZMod 539096783161) ^ 31711575480 = ((298523788964 : ℕ) : ZMod 539096783161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (539096783161 - 1) / 509 = 1059129240 from by norm_num]
      have h2 : (7 : ZMod 539096783161) ^ 1059129240 = ((121860344911 : ℕ) : ZMod 539096783161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (539096783161 - 1) / 39937 = 13498680 from by norm_num]
      have h2 : (7 : ZMod 539096783161) ^ 13498680 = ((506710691491 : ℕ) : ZMod 539096783161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_38506913083 : Nat.Prime 38506913083 := by
  refine lucas_primality 38506913083 (2 : ZMod 38506913083) ?_ (fun q hq hd => ?_)
  · rw [show 38506913083 - 1 = 38506913082 from by norm_num]
    reduce_mod_char
  · have e : 38506913083 - 1 = [2 ^ 1, 3 ^ 3, 11 ^ 1, 41 ^ 1, 67 ^ 1, 23599 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38506913083 - 1) / 2 = 19253456541 from by norm_num]
      have h2 : (2 : ZMod 38506913083) ^ 19253456541 = ((38506913082 : ℕ) : ZMod 38506913083) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38506913083 - 1) / 3 = 12835637694 from by norm_num]
      have h2 : (2 : ZMod 38506913083) ^ 12835637694 = ((38506393902 : ℕ) : ZMod 38506913083) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38506913083 - 1) / 11 = 3500628462 from by norm_num]
      have h2 : (2 : ZMod 38506913083) ^ 3500628462 = ((27305166917 : ℕ) : ZMod 38506913083) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38506913083 - 1) / 41 = 939193002 from by norm_num]
      have h2 : (2 : ZMod 38506913083) ^ 939193002 = ((5931074805 : ℕ) : ZMod 38506913083) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38506913083 - 1) / 67 = 574730046 from by norm_num]
      have h2 : (2 : ZMod 38506913083) ^ 574730046 = ((15712787881 : ℕ) : ZMod 38506913083) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38506913083 - 1) / 23599 = 1631718 from by norm_num]
      have h2 : (2 : ZMod 38506913083) ^ 1631718 = ((10940550062 : ℕ) : ZMod 38506913083) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_126667477 : Nat.Prime 126667477 := by
  refine lucas_primality 126667477 (2 : ZMod 126667477) ?_ (fun q hq hd => ?_)
  · rw [show 126667477 - 1 = 126667476 from by norm_num]
    reduce_mod_char
  · have e : 126667477 - 1 = [2 ^ 2, 3 ^ 4, 13 ^ 1, 17 ^ 1, 29 ^ 1, 61 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126667477 - 1) / 2 = 63333738 from by norm_num]
      have h2 : (2 : ZMod 126667477) ^ 63333738 = ((126667476 : ℕ) : ZMod 126667477) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126667477 - 1) / 3 = 42222492 from by norm_num]
      have h2 : (2 : ZMod 126667477) ^ 42222492 = ((53067400 : ℕ) : ZMod 126667477) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126667477 - 1) / 13 = 9743652 from by norm_num]
      have h2 : (2 : ZMod 126667477) ^ 9743652 = ((16539039 : ℕ) : ZMod 126667477) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126667477 - 1) / 17 = 7451028 from by norm_num]
      have h2 : (2 : ZMod 126667477) ^ 7451028 = ((125849595 : ℕ) : ZMod 126667477) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126667477 - 1) / 29 = 4367844 from by norm_num]
      have h2 : (2 : ZMod 126667477) ^ 4367844 = ((75530078 : ℕ) : ZMod 126667477) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126667477 - 1) / 61 = 2076516 from by norm_num]
      have h2 : (2 : ZMod 126667477) ^ 2076516 = ((88298357 : ℕ) : ZMod 126667477) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_506669909 : Nat.Prime 506669909 := by
  refine lucas_primality 506669909 (2 : ZMod 506669909) ?_ (fun q hq hd => ?_)
  · rw [show 506669909 - 1 = 506669908 from by norm_num]
    reduce_mod_char
  · have e : 506669909 - 1 = [2 ^ 2, 126667477 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (506669909 - 1) / 2 = 253334954 from by norm_num]
      have h2 : (2 : ZMod 506669909) ^ 253334954 = ((506669908 : ℕ) : ZMod 506669909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_126667477).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (506669909 - 1) / 126667477 = 4 from by norm_num]
      have h2 : (2 : ZMod 506669909) ^ 4 = ((16 : ℕ) : ZMod 506669909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1550435471521 : Nat.Prime 1550435471521 := by
  refine lucas_primality 1550435471521 (11 : ZMod 1550435471521) ?_ (fun q hq hd => ?_)
  · rw [show 1550435471521 - 1 = 1550435471520 from by norm_num]
    reduce_mod_char
  · have e : 1550435471521 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 13 ^ 1, 17 ^ 1, 83 ^ 1, 293 ^ 1, 601 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1550435471521 - 1) / 2 = 775217735760 from by norm_num]
      have h2 : (11 : ZMod 1550435471521) ^ 775217735760 = ((1550435471520 : ℕ) : ZMod 1550435471521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1550435471521 - 1) / 3 = 516811823840 from by norm_num]
      have h2 : (11 : ZMod 1550435471521) ^ 516811823840 = ((981275232628 : ℕ) : ZMod 1550435471521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1550435471521 - 1) / 5 = 310087094304 from by norm_num]
      have h2 : (11 : ZMod 1550435471521) ^ 310087094304 = ((790501186673 : ℕ) : ZMod 1550435471521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1550435471521 - 1) / 13 = 119264267040 from by norm_num]
      have h2 : (11 : ZMod 1550435471521) ^ 119264267040 = ((399399614845 : ℕ) : ZMod 1550435471521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1550435471521 - 1) / 17 = 91202086560 from by norm_num]
      have h2 : (11 : ZMod 1550435471521) ^ 91202086560 = ((184802124787 : ℕ) : ZMod 1550435471521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1550435471521 - 1) / 83 = 18679945440 from by norm_num]
      have h2 : (11 : ZMod 1550435471521) ^ 18679945440 = ((495136067724 : ℕ) : ZMod 1550435471521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1550435471521 - 1) / 293 = 5291588640 from by norm_num]
      have h2 : (11 : ZMod 1550435471521) ^ 5291588640 = ((1087792822849 : ℕ) : ZMod 1550435471521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1550435471521 - 1) / 601 = 2579759520 from by norm_num]
      have h2 : (11 : ZMod 1550435471521) ^ 2579759520 = ((1309286522805 : ℕ) : ZMod 1550435471521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_110745390823 : Nat.Prime 110745390823 := by
  refine lucas_primality 110745390823 (3 : ZMod 110745390823) ?_ (fun q hq hd => ?_)
  · rw [show 110745390823 - 1 = 110745390822 from by norm_num]
    reduce_mod_char
  · have e : 110745390823 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 31 ^ 1, 1291 ^ 1, 41927 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110745390823 - 1) / 2 = 55372695411 from by norm_num]
      have h2 : (3 : ZMod 110745390823) ^ 55372695411 = ((110745390822 : ℕ) : ZMod 110745390823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110745390823 - 1) / 3 = 36915130274 from by norm_num]
      have h2 : (3 : ZMod 110745390823) ^ 36915130274 = ((110744510358 : ℕ) : ZMod 110745390823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110745390823 - 1) / 11 = 10067762802 from by norm_num]
      have h2 : (3 : ZMod 110745390823) ^ 10067762802 = ((56767834353 : ℕ) : ZMod 110745390823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110745390823 - 1) / 31 = 3572431962 from by norm_num]
      have h2 : (3 : ZMod 110745390823) ^ 3572431962 = ((97312408426 : ℕ) : ZMod 110745390823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110745390823 - 1) / 1291 = 85782642 from by norm_num]
      have h2 : (3 : ZMod 110745390823) ^ 85782642 = ((101659693928 : ℕ) : ZMod 110745390823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110745390823 - 1) / 41927 = 2641386 from by norm_num]
      have h2 : (3 : ZMod 110745390823) ^ 2641386 = ((54181353423 : ℕ) : ZMod 110745390823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_13843173853 : Nat.Prime 13843173853 := by
  refine lucas_primality 13843173853 (2 : ZMod 13843173853) ?_ (fun q hq hd => ?_)
  · rw [show 13843173853 - 1 = 13843173852 from by norm_num]
    reduce_mod_char
  · have e : 13843173853 - 1 = [2 ^ 2, 3 ^ 2, 23 ^ 1, 16718809 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13843173853 - 1) / 2 = 6921586926 from by norm_num]
      have h2 : (2 : ZMod 13843173853) ^ 6921586926 = ((13843173852 : ℕ) : ZMod 13843173853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13843173853 - 1) / 3 = 4614391284 from by norm_num]
      have h2 : (2 : ZMod 13843173853) ^ 4614391284 = ((11200778917 : ℕ) : ZMod 13843173853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13843173853 - 1) / 23 = 601877124 from by norm_num]
      have h2 : (2 : ZMod 13843173853) ^ 601877124 = ((4545897797 : ℕ) : ZMod 13843173853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13843173853 - 1) / 16718809 = 828 from by norm_num]
      have h2 : (2 : ZMod 13843173853) ^ 828 = ((2132639028 : ℕ) : ZMod 13843173853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6921586927 : Nat.Prime 6921586927 := by
  refine lucas_primality 6921586927 (5 : ZMod 6921586927) ?_ (fun q hq hd => ?_)
  · rw [show 6921586927 - 1 = 6921586926 from by norm_num]
    reduce_mod_char
  · have e : 6921586927 - 1 = [2 ^ 1, 3 ^ 2, 23 ^ 1, 16718809 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6921586927 - 1) / 2 = 3460793463 from by norm_num]
      have h2 : (5 : ZMod 6921586927) ^ 3460793463 = ((6921586926 : ℕ) : ZMod 6921586927) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6921586927 - 1) / 3 = 2307195642 from by norm_num]
      have h2 : (5 : ZMod 6921586927) ^ 2307195642 = ((5942044170 : ℕ) : ZMod 6921586927) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6921586927 - 1) / 23 = 300938562 from by norm_num]
      have h2 : (5 : ZMod 6921586927) ^ 300938562 = ((4572505565 : ℕ) : ZMod 6921586927) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6921586927 - 1) / 16718809 = 414 from by norm_num]
      have h2 : (5 : ZMod 6921586927) ^ 414 = ((692618613 : ℕ) : ZMod 6921586927) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_432599183 : Nat.Prime 432599183 := by
  refine lucas_primality 432599183 (5 : ZMod 432599183) ?_ (fun q hq hd => ?_)
  · rw [show 432599183 - 1 = 432599182 from by norm_num]
    reduce_mod_char
  · have e : 432599183 - 1 = [2 ^ 1, 19 ^ 1, 11384189 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (432599183 - 1) / 2 = 216299591 from by norm_num]
      have h2 : (5 : ZMod 432599183) ^ 216299591 = ((432599182 : ℕ) : ZMod 432599183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (432599183 - 1) / 19 = 22768378 from by norm_num]
      have h2 : (5 : ZMod 432599183) ^ 22768378 = ((109890343 : ℕ) : ZMod 432599183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (432599183 - 1) / 11384189 = 38 from by norm_num]
      have h2 : (5 : ZMod 432599183) ^ 38 = ((206263670 : ℕ) : ZMod 432599183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1106131489 : Nat.Prime 1106131489 := by
  refine lucas_primality 1106131489 (19 : ZMod 1106131489) ?_ (fun q hq hd => ?_)
  · rw [show 1106131489 - 1 = 1106131488 from by norm_num]
    reduce_mod_char
  · have e : 1106131489 - 1 = [2 ^ 5, 3 ^ 1, 7 ^ 2, 11 ^ 1, 21377 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1106131489 - 1) / 2 = 553065744 from by norm_num]
      have h2 : (19 : ZMod 1106131489) ^ 553065744 = ((1106131488 : ℕ) : ZMod 1106131489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1106131489 - 1) / 3 = 368710496 from by norm_num]
      have h2 : (19 : ZMod 1106131489) ^ 368710496 = ((214358880 : ℕ) : ZMod 1106131489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1106131489 - 1) / 7 = 158018784 from by norm_num]
      have h2 : (19 : ZMod 1106131489) ^ 158018784 = ((418769631 : ℕ) : ZMod 1106131489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1106131489 - 1) / 11 = 100557408 from by norm_num]
      have h2 : (19 : ZMod 1106131489) ^ 100557408 = ((21517157 : ℕ) : ZMod 1106131489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1106131489 - 1) / 21377 = 51744 from by norm_num]
      have h2 : (19 : ZMod 1106131489) ^ 51744 = ((107990146 : ℕ) : ZMod 1106131489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_97010607829826070873559937268360584022789501553441 : Nat.Prime 97010607829826070873559937268360584022789501553441 := by
  refine lucas_primality 97010607829826070873559937268360584022789501553441 (41 : ZMod 97010607829826070873559937268360584022789501553441) ?_ (fun q hq hd => ?_)
  · rw [show 97010607829826070873559937268360584022789501553441 - 1 = 97010607829826070873559937268360584022789501553440 from by norm_num]
    reduce_mod_char
  · have e : 97010607829826070873559937268360584022789501553441 - 1 = [2 ^ 5, 3 ^ 2, 5 ^ 1, 7 ^ 1, 11 ^ 4, 13 ^ 1, 17 ^ 1, 19 ^ 1, 37 ^ 1, 61 ^ 1, 97 ^ 1, 241 ^ 1, 1117 ^ 1, 1777 ^ 1, 10657 ^ 1, 20113 ^ 1, 6304673 ^ 1, 1106131489 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 2 = 48505303914913035436779968634180292011394750776720 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 48505303914913035436779968634180292011394750776720 = ((97010607829826070873559937268360584022789501553440 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 3 = 32336869276608690291186645756120194674263167184480 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 32336869276608690291186645756120194674263167184480 = ((41588259930519852082339036225121743736785072100327 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 5 = 19402121565965214174711987453672116804557900310688 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 19402121565965214174711987453672116804557900310688 = ((51956181670765289313486406521842266140399024423907 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 7 = 13858658261403724410508562466908654860398500221920 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 13858658261403724410508562466908654860398500221920 = ((46704926801621585203927435304664514717428024526481 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 11 = 8819146166347824624869085206214598547526318323040 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 8819146166347824624869085206214598547526318323040 = ((71323194281345855837758276442340430794549469039135 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 13 = 7462354448448159297966149020643121847906884734880 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 7462354448448159297966149020643121847906884734880 = ((97010607829795158193027066595724910669852614100080 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 17 = 5706506342930945345503525721668269648399382444320 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 5706506342930945345503525721668269648399382444320 = ((85644142617840344583212890962331606126137368166386 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 19 = 5105821464727687940713680908861083369620500081760 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 5105821464727687940713680908861083369620500081760 = ((34653736098954675841261197766826069148335159262738 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 37 = 2621908319725028942528646953198934703318635177120 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 2621908319725028942528646953198934703318635177120 = ((69224769860548574797944683994921964560024634765999 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 61 = 1590337833275837227435408807678042361029336091040 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 1590337833275837227435408807678042361029336091040 = ((17380848035445116296858025590348543422711205195397 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 97 = 1000109359070371864675875641941861690956592799520 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 1000109359070371864675875641941861690956592799520 = ((93652714815457928168449088121966126895352672226811 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 241 = 402533642447411082462904304018093709638130711840 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 402533642447411082462904304018093709638130711840 = ((60760908263955347592820936535636904150772030457630 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 1117 = 86849246042816536144637365504351462867313788320 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 86849246042816536144637365504351462867313788320 = ((35132333644306218144075717038977823951117267750650 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 1777 = 54592351057864980795475485238244560508041362720 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 54592351057864980795475485238244560508041362720 = ((85761891467585223301949463502296213286164783659956 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 10657 = 9102994072424328692273617084391534580349957920 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 9102994072424328692273617084391534580349957920 = ((88627964249565742304480992850041891305976128130670 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 20113 = 4823278865898974338664542199988096456162158880 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 4823278865898974338664542199988096456162158880 = ((14004376842777511819748362202339958757727503758107 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 6304673 = 15387095862041706346000805635496176252565280 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 15387095862041706346000805635496176252565280 = ((94974942817151522578052277053168161180396171655560 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1106131489).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97010607829826070873559937268360584022789501553441 - 1) / 1106131489 = 87702600273615455199793102778543703516960 from by norm_num]
      have h2 : (41 : ZMod 97010607829826070873559937268360584022789501553441) ^ 87702600273615455199793102778543703516960 = ((62134773795751610908235668403160005910021564442761 : ℕ) : ZMod 97010607829826070873559937268360584022789501553441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_149441953 : Nat.Prime 149441953 := by
  refine lucas_primality 149441953 (7 : ZMod 149441953) ?_ (fun q hq hd => ?_)
  · rw [show 149441953 - 1 = 149441952 from by norm_num]
    reduce_mod_char
  · have e : 149441953 - 1 = [2 ^ 5, 3 ^ 1, 11 ^ 1, 47 ^ 1, 3011 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (149441953 - 1) / 2 = 74720976 from by norm_num]
      have h2 : (7 : ZMod 149441953) ^ 74720976 = ((149441952 : ℕ) : ZMod 149441953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (149441953 - 1) / 3 = 49813984 from by norm_num]
      have h2 : (7 : ZMod 149441953) ^ 49813984 = ((135125922 : ℕ) : ZMod 149441953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (149441953 - 1) / 11 = 13585632 from by norm_num]
      have h2 : (7 : ZMod 149441953) ^ 13585632 = ((128507560 : ℕ) : ZMod 149441953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (149441953 - 1) / 47 = 3179616 from by norm_num]
      have h2 : (7 : ZMod 149441953) ^ 3179616 = ((110250032 : ℕ) : ZMod 149441953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (149441953 - 1) / 3011 = 49632 from by norm_num]
      have h2 : (7 : ZMod 149441953) ^ 49632 = ((22064920 : ℕ) : ZMod 149441953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_153805720391 : Nat.Prime 153805720391 := by
  refine lucas_primality 153805720391 (11 : ZMod 153805720391) ?_ (fun q hq hd => ?_)
  · rw [show 153805720391 - 1 = 153805720390 from by norm_num]
    reduce_mod_char
  · have e : 153805720391 - 1 = [2 ^ 1, 5 ^ 1, 7 ^ 1, 157 ^ 1, 13995061 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (153805720391 - 1) / 2 = 76902860195 from by norm_num]
      have h2 : (11 : ZMod 153805720391) ^ 76902860195 = ((153805720390 : ℕ) : ZMod 153805720391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (153805720391 - 1) / 5 = 30761144078 from by norm_num]
      have h2 : (11 : ZMod 153805720391) ^ 30761144078 = ((107040623973 : ℕ) : ZMod 153805720391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (153805720391 - 1) / 7 = 21972245770 from by norm_num]
      have h2 : (11 : ZMod 153805720391) ^ 21972245770 = ((27952087024 : ℕ) : ZMod 153805720391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (153805720391 - 1) / 157 = 979654270 from by norm_num]
      have h2 : (11 : ZMod 153805720391) ^ 979654270 = ((138369353622 : ℕ) : ZMod 153805720391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (153805720391 - 1) / 13995061 = 10990 from by norm_num]
      have h2 : (11 : ZMod 153805720391) ^ 10990 = ((143428050334 : ℕ) : ZMod 153805720391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_20346651139084609 : Nat.Prime 20346651139084609 := by
  refine lucas_primality 20346651139084609 (7 : ZMod 20346651139084609) ?_ (fun q hq hd => ?_)
  · rw [show 20346651139084609 - 1 = 20346651139084608 from by norm_num]
    reduce_mod_char
  · have e : 20346651139084609 - 1 = [2 ^ 6, 3 ^ 1, 13 ^ 1, 53 ^ 1, 153805720391 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20346651139084609 - 1) / 2 = 10173325569542304 from by norm_num]
      have h2 : (7 : ZMod 20346651139084609) ^ 10173325569542304 = ((20346651139084608 : ℕ) : ZMod 20346651139084609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20346651139084609 - 1) / 3 = 6782217046361536 from by norm_num]
      have h2 : (7 : ZMod 20346651139084609) ^ 6782217046361536 = ((1594108742539688 : ℕ) : ZMod 20346651139084609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20346651139084609 - 1) / 13 = 1565127010698816 from by norm_num]
      have h2 : (7 : ZMod 20346651139084609) ^ 1565127010698816 = ((11221234509933754 : ℕ) : ZMod 20346651139084609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20346651139084609 - 1) / 53 = 383899078095936 from by norm_num]
      have h2 : (7 : ZMod 20346651139084609) ^ 383899078095936 = ((6962415286306529 : ℕ) : ZMod 20346651139084609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_153805720391).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20346651139084609 - 1) / 153805720391 = 132288 from by norm_num]
      have h2 : (7 : ZMod 20346651139084609) ^ 132288 = ((17404329968360973 : ℕ) : ZMod 20346651139084609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5624354543 : Nat.Prime 5624354543 := by
  refine lucas_primality 5624354543 (5 : ZMod 5624354543) ?_ (fun q hq hd => ?_)
  · rw [show 5624354543 - 1 = 5624354542 from by norm_num]
    reduce_mod_char
  · have e : 5624354543 - 1 = [2 ^ 1, 23 ^ 1, 181 ^ 1, 463 ^ 1, 1459 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5624354543 - 1) / 2 = 2812177271 from by norm_num]
      have h2 : (5 : ZMod 5624354543) ^ 2812177271 = ((5624354542 : ℕ) : ZMod 5624354543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5624354543 - 1) / 23 = 244537154 from by norm_num]
      have h2 : (5 : ZMod 5624354543) ^ 244537154 = ((757559236 : ℕ) : ZMod 5624354543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5624354543 - 1) / 181 = 31073782 from by norm_num]
      have h2 : (5 : ZMod 5624354543) ^ 31073782 = ((3195783429 : ℕ) : ZMod 5624354543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5624354543 - 1) / 463 = 12147634 from by norm_num]
      have h2 : (5 : ZMod 5624354543) ^ 12147634 = ((1496918782 : ℕ) : ZMod 5624354543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5624354543 - 1) / 1459 = 3854938 from by norm_num]
      have h2 : (5 : ZMod 5624354543) ^ 3854938 = ((719036123 : ℕ) : ZMod 5624354543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2368730543 : Nat.Prime 2368730543 := by
  refine lucas_primality 2368730543 (5 : ZMod 2368730543) ?_ (fun q hq hd => ?_)
  · rw [show 2368730543 - 1 = 2368730542 from by norm_num]
    reduce_mod_char
  · have e : 2368730543 - 1 = [2 ^ 1, 71 ^ 1, 2851 ^ 1, 5851 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2368730543 - 1) / 2 = 1184365271 from by norm_num]
      have h2 : (5 : ZMod 2368730543) ^ 1184365271 = ((2368730542 : ℕ) : ZMod 2368730543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2368730543 - 1) / 71 = 33362402 from by norm_num]
      have h2 : (5 : ZMod 2368730543) ^ 33362402 = ((250548053 : ℕ) : ZMod 2368730543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2368730543 - 1) / 2851 = 830842 from by norm_num]
      have h2 : (5 : ZMod 2368730543) ^ 830842 = ((1952624071 : ℕ) : ZMod 2368730543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2368730543 - 1) / 5851 = 404842 from by norm_num]
      have h2 : (5 : ZMod 2368730543) ^ 404842 = ((1773420563 : ℕ) : ZMod 2368730543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_117567026551063291227924640993 : Nat.Prime 117567026551063291227924640993 := by
  refine lucas_primality 117567026551063291227924640993 (5 : ZMod 117567026551063291227924640993) ?_ (fun q hq hd => ?_)
  · rw [show 117567026551063291227924640993 - 1 = 117567026551063291227924640992 from by norm_num]
    reduce_mod_char
  · have e : 117567026551063291227924640993 - 1 = [2 ^ 5, 3 ^ 1, 79 ^ 1, 1163587 ^ 1, 2368730543 ^ 1, 5624354543 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (117567026551063291227924640993 - 1) / 2 = 58783513275531645613962320496 from by norm_num]
      have h2 : (5 : ZMod 117567026551063291227924640993) ^ 58783513275531645613962320496 = ((117567026551063291227924640992 : ℕ) : ZMod 117567026551063291227924640993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (117567026551063291227924640993 - 1) / 3 = 39189008850354430409308213664 from by norm_num]
      have h2 : (5 : ZMod 117567026551063291227924640993) ^ 39189008850354430409308213664 = ((81391711922142456144596722522 : ℕ) : ZMod 117567026551063291227924640993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (117567026551063291227924640993 - 1) / 79 = 1488190209507130268707906848 from by norm_num]
      have h2 : (5 : ZMod 117567026551063291227924640993) ^ 1488190209507130268707906848 = ((26508192412915377490121658850 : ℕ) : ZMod 117567026551063291227924640993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (117567026551063291227924640993 - 1) / 1163587 = 101038449682802653542816 from by norm_num]
      have h2 : (5 : ZMod 117567026551063291227924640993) ^ 101038449682802653542816 = ((23834645564354682445040220308 : ℕ) : ZMod 117567026551063291227924640993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2368730543).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (117567026551063291227924640993 - 1) / 2368730543 = 49632925491881619744 from by norm_num]
      have h2 : (5 : ZMod 117567026551063291227924640993) ^ 49632925491881619744 = ((108943748835101924830737330117 : ℕ) : ZMod 117567026551063291227924640993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_5624354543).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (117567026551063291227924640993 - 1) / 5624354543 = 20903203319105427744 from by norm_num]
      have h2 : (5 : ZMod 117567026551063291227924640993) ^ 20903203319105427744 = ((93136052506767810839401501441 : ℕ) : ZMod 117567026551063291227924640993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_335786251793 : Nat.Prime 335786251793 := by
  refine lucas_primality 335786251793 (3 : ZMod 335786251793) ?_ (fun q hq hd => ?_)
  · rw [show 335786251793 - 1 = 335786251792 from by norm_num]
    reduce_mod_char
  · have e : 335786251793 - 1 = [2 ^ 4, 47 ^ 1, 97 ^ 1, 179 ^ 1, 25717 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (335786251793 - 1) / 2 = 167893125896 from by norm_num]
      have h2 : (3 : ZMod 335786251793) ^ 167893125896 = ((335786251792 : ℕ) : ZMod 335786251793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (335786251793 - 1) / 47 = 7144388336 from by norm_num]
      have h2 : (3 : ZMod 335786251793) ^ 7144388336 = ((256715117588 : ℕ) : ZMod 335786251793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (335786251793 - 1) / 97 = 3461713936 from by norm_num]
      have h2 : (3 : ZMod 335786251793) ^ 3461713936 = ((153625859029 : ℕ) : ZMod 335786251793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (335786251793 - 1) / 179 = 1875900848 from by norm_num]
      have h2 : (3 : ZMod 335786251793) ^ 1875900848 = ((202040897494 : ℕ) : ZMod 335786251793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (335786251793 - 1) / 25717 = 13056976 from by norm_num]
      have h2 : (3 : ZMod 335786251793) ^ 13056976 = ((199703725429 : ℕ) : ZMod 335786251793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_74881819 : Nat.Prime 74881819 := by
  refine lucas_primality 74881819 (2 : ZMod 74881819) ?_ (fun q hq hd => ?_)
  · rw [show 74881819 - 1 = 74881818 from by norm_num]
    reduce_mod_char
  · have e : 74881819 - 1 = [2 ^ 1, 3 ^ 2, 11 ^ 2, 34381 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74881819 - 1) / 2 = 37440909 from by norm_num]
      have h2 : (2 : ZMod 74881819) ^ 37440909 = ((74881818 : ℕ) : ZMod 74881819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74881819 - 1) / 3 = 24960606 from by norm_num]
      have h2 : (2 : ZMod 74881819) ^ 24960606 = ((26258854 : ℕ) : ZMod 74881819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74881819 - 1) / 11 = 6807438 from by norm_num]
      have h2 : (2 : ZMod 74881819) ^ 6807438 = ((59562779 : ℕ) : ZMod 74881819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74881819 - 1) / 34381 = 2178 from by norm_num]
      have h2 : (2 : ZMod 74881819) ^ 2178 = ((20155030 : ℕ) : ZMod 74881819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2545981847 : Nat.Prime 2545981847 := by
  refine lucas_primality 2545981847 (5 : ZMod 2545981847) ?_ (fun q hq hd => ?_)
  · rw [show 2545981847 - 1 = 2545981846 from by norm_num]
    reduce_mod_char
  · have e : 2545981847 - 1 = [2 ^ 1, 17 ^ 1, 74881819 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2545981847 - 1) / 2 = 1272990923 from by norm_num]
      have h2 : (5 : ZMod 2545981847) ^ 1272990923 = ((2545981846 : ℕ) : ZMod 2545981847) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2545981847 - 1) / 17 = 149763638 from by norm_num]
      have h2 : (5 : ZMod 2545981847) ^ 149763638 = ((2318340418 : ℕ) : ZMod 2545981847) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_74881819).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2545981847 - 1) / 74881819 = 34 from by norm_num]
      have h2 : (5 : ZMod 2545981847) ^ 34 = ((1072299233 : ℕ) : ZMod 2545981847) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_35643745859 : Nat.Prime 35643745859 := by
  refine lucas_primality 35643745859 (2 : ZMod 35643745859) ?_ (fun q hq hd => ?_)
  · rw [show 35643745859 - 1 = 35643745858 from by norm_num]
    reduce_mod_char
  · have e : 35643745859 - 1 = [2 ^ 1, 7 ^ 1, 2545981847 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35643745859 - 1) / 2 = 17821872929 from by norm_num]
      have h2 : (2 : ZMod 35643745859) ^ 17821872929 = ((35643745858 : ℕ) : ZMod 35643745859) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35643745859 - 1) / 7 = 5091963694 from by norm_num]
      have h2 : (2 : ZMod 35643745859) ^ 5091963694 = ((16838009276 : ℕ) : ZMod 35643745859) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2545981847).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35643745859 - 1) / 2545981847 = 14 from by norm_num]
      have h2 : (2 : ZMod 35643745859) ^ 14 = ((16384 : ℕ) : ZMod 35643745859) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3437268988166807 : Nat.Prime 3437268988166807 := by
  refine lucas_primality 3437268988166807 (5 : ZMod 3437268988166807) ?_ (fun q hq hd => ?_)
  · rw [show 3437268988166807 - 1 = 3437268988166806 from by norm_num]
    reduce_mod_char
  · have e : 3437268988166807 - 1 = [2 ^ 1, 13 ^ 1, 3709 ^ 1, 35643745859 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3437268988166807 - 1) / 2 = 1718634494083403 from by norm_num]
      have h2 : (5 : ZMod 3437268988166807) ^ 1718634494083403 = ((3437268988166806 : ℕ) : ZMod 3437268988166807) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3437268988166807 - 1) / 13 = 264405306782062 from by norm_num]
      have h2 : (5 : ZMod 3437268988166807) ^ 264405306782062 = ((645124320482039 : ℕ) : ZMod 3437268988166807) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3437268988166807 - 1) / 3709 = 926737392334 from by norm_num]
      have h2 : (5 : ZMod 3437268988166807) ^ 926737392334 = ((3243348319721273 : ℕ) : ZMod 3437268988166807) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_35643745859).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3437268988166807 - 1) / 35643745859 = 96434 from by norm_num]
      have h2 : (5 : ZMod 3437268988166807) ^ 96434 = ((2054488591261815 : ℕ) : ZMod 3437268988166807) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2728049689 : Nat.Prime 2728049689 := by
  refine lucas_primality 2728049689 (11 : ZMod 2728049689) ?_ (fun q hq hd => ?_)
  · rw [show 2728049689 - 1 = 2728049688 from by norm_num]
    reduce_mod_char
  · have e : 2728049689 - 1 = [2 ^ 3, 3 ^ 2, 7 ^ 1, 13 ^ 1, 23 ^ 1, 43 ^ 1, 421 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2728049689 - 1) / 2 = 1364024844 from by norm_num]
      have h2 : (11 : ZMod 2728049689) ^ 1364024844 = ((2728049688 : ℕ) : ZMod 2728049689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2728049689 - 1) / 3 = 909349896 from by norm_num]
      have h2 : (11 : ZMod 2728049689) ^ 909349896 = ((2635270068 : ℕ) : ZMod 2728049689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2728049689 - 1) / 7 = 389721384 from by norm_num]
      have h2 : (11 : ZMod 2728049689) ^ 389721384 = ((677396255 : ℕ) : ZMod 2728049689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2728049689 - 1) / 13 = 209849976 from by norm_num]
      have h2 : (11 : ZMod 2728049689) ^ 209849976 = ((615475981 : ℕ) : ZMod 2728049689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2728049689 - 1) / 23 = 118610856 from by norm_num]
      have h2 : (11 : ZMod 2728049689) ^ 118610856 = ((953354709 : ℕ) : ZMod 2728049689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2728049689 - 1) / 43 = 63443016 from by norm_num]
      have h2 : (11 : ZMod 2728049689) ^ 63443016 = ((63897463 : ℕ) : ZMod 2728049689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2728049689 - 1) / 421 = 6479928 from by norm_num]
      have h2 : (11 : ZMod 2728049689) ^ 6479928 = ((171471213 : ℕ) : ZMod 2728049689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_62327847687645911640969067843358449 : Nat.Prime 62327847687645911640969067843358449 := by
  refine lucas_primality 62327847687645911640969067843358449 (7 : ZMod 62327847687645911640969067843358449) ?_ (fun q hq hd => ?_)
  · rw [show 62327847687645911640969067843358449 - 1 = 62327847687645911640969067843358448 from by norm_num]
    reduce_mod_char
  · have e : 62327847687645911640969067843358449 - 1 = [2 ^ 4, 3 ^ 3, 103 ^ 1, 149381 ^ 1, 2728049689 ^ 1, 3437268988166807 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62327847687645911640969067843358449 - 1) / 2 = 31163923843822955820484533921679224 from by norm_num]
      have h2 : (7 : ZMod 62327847687645911640969067843358449) ^ 31163923843822955820484533921679224 = ((62327847687645911640969067843358448 : ℕ) : ZMod 62327847687645911640969067843358449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62327847687645911640969067843358449 - 1) / 3 = 20775949229215303880323022614452816 from by norm_num]
      have h2 : (7 : ZMod 62327847687645911640969067843358449) ^ 20775949229215303880323022614452816 = ((45210633983840619976532107441039374 : ℕ) : ZMod 62327847687645911640969067843358449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62327847687645911640969067843358449 - 1) / 103 = 605124734831513705252126872265616 from by norm_num]
      have h2 : (7 : ZMod 62327847687645911640969067843358449) ^ 605124734831513705252126872265616 = ((35847166813472900956690797577292545 : ℕ) : ZMod 62327847687645911640969067843358449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62327847687645911640969067843358449 - 1) / 149381 = 417240798278535500772983631408 from by norm_num]
      have h2 : (7 : ZMod 62327847687645911640969067843358449) ^ 417240798278535500772983631408 = ((56414332993808022260307240624296058 : ℕ) : ZMod 62327847687645911640969067843358449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2728049689).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62327847687645911640969067843358449 - 1) / 2728049689 = 22847035352385002559595632 from by norm_num]
      have h2 : (7 : ZMod 62327847687645911640969067843358449) ^ 22847035352385002559595632 = ((53761831321984079306945208822103445 : ℕ) : ZMod 62327847687645911640969067843358449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3437268988166807).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62327847687645911640969067843358449 - 1) / 3437268988166807 = 18132956106204280464 from by norm_num]
      have h2 : (7 : ZMod 62327847687645911640969067843358449) ^ 18132956106204280464 = ((6865105319910953773750873837063387 : ℕ) : ZMod 62327847687645911640969067843358449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_46566307 : Nat.Prime 46566307 := by
  refine lucas_primality 46566307 (19 : ZMod 46566307) ?_ (fun q hq hd => ?_)
  · rw [show 46566307 - 1 = 46566306 from by norm_num]
    reduce_mod_char
  · have e : 46566307 - 1 = [2 ^ 1, 3 ^ 3, 23 ^ 1, 37493 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46566307 - 1) / 2 = 23283153 from by norm_num]
      have h2 : (19 : ZMod 46566307) ^ 23283153 = ((46566306 : ℕ) : ZMod 46566307) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46566307 - 1) / 3 = 15522102 from by norm_num]
      have h2 : (19 : ZMod 46566307) ^ 15522102 = ((11954582 : ℕ) : ZMod 46566307) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46566307 - 1) / 23 = 2024622 from by norm_num]
      have h2 : (19 : ZMod 46566307) ^ 2024622 = ((18993886 : ℕ) : ZMod 46566307) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46566307 - 1) / 37493 = 1242 from by norm_num]
      have h2 : (19 : ZMod 46566307) ^ 1242 = ((33990796 : ℕ) : ZMod 46566307) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1436269938872009 : Nat.Prime 1436269938872009 := by
  refine lucas_primality 1436269938872009 (3 : ZMod 1436269938872009) ?_ (fun q hq hd => ?_)
  · rw [show 1436269938872009 - 1 = 1436269938872008 from by norm_num]
    reduce_mod_char
  · have e : 1436269938872009 - 1 = [2 ^ 3, 139 ^ 1, 27737 ^ 1, 46566307 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1436269938872009 - 1) / 2 = 718134969436004 from by norm_num]
      have h2 : (3 : ZMod 1436269938872009) ^ 718134969436004 = ((1436269938872008 : ℕ) : ZMod 1436269938872009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1436269938872009 - 1) / 139 = 10332877258072 from by norm_num]
      have h2 : (3 : ZMod 1436269938872009) ^ 10332877258072 = ((1121358029531489 : ℕ) : ZMod 1436269938872009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1436269938872009 - 1) / 27737 = 51781733384 from by norm_num]
      have h2 : (3 : ZMod 1436269938872009) ^ 51781733384 = ((1345603694127958 : ℕ) : ZMod 1436269938872009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_46566307).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1436269938872009 - 1) / 46566307 = 30843544 from by norm_num]
      have h2 : (3 : ZMod 1436269938872009) ^ 30843544 = ((243722423934252 : ℕ) : ZMod 1436269938872009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_42232714889 : Nat.Prime 42232714889 := by
  refine lucas_primality 42232714889 (3 : ZMod 42232714889) ?_ (fun q hq hd => ?_)
  · rw [show 42232714889 - 1 = 42232714888 from by norm_num]
    reduce_mod_char
  · have e : 42232714889 - 1 = [2 ^ 3, 7 ^ 1, 13 ^ 1, 157 ^ 1, 541 ^ 1, 683 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42232714889 - 1) / 2 = 21116357444 from by norm_num]
      have h2 : (3 : ZMod 42232714889) ^ 21116357444 = ((42232714888 : ℕ) : ZMod 42232714889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42232714889 - 1) / 7 = 6033244984 from by norm_num]
      have h2 : (3 : ZMod 42232714889) ^ 6033244984 = ((21750102050 : ℕ) : ZMod 42232714889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42232714889 - 1) / 13 = 3248670376 from by norm_num]
      have h2 : (3 : ZMod 42232714889) ^ 3248670376 = ((6578335402 : ℕ) : ZMod 42232714889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42232714889 - 1) / 157 = 268998184 from by norm_num]
      have h2 : (3 : ZMod 42232714889) ^ 268998184 = ((15258687175 : ℕ) : ZMod 42232714889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42232714889 - 1) / 541 = 78064168 from by norm_num]
      have h2 : (3 : ZMod 42232714889) ^ 78064168 = ((13972233648 : ℕ) : ZMod 42232714889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42232714889 - 1) / 683 = 61834136 from by norm_num]
      have h2 : (3 : ZMod 42232714889) ^ 61834136 = ((5756860348 : ℕ) : ZMod 42232714889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_33307648393 : Nat.Prime 33307648393 := by
  refine lucas_primality 33307648393 (7 : ZMod 33307648393) ?_ (fun q hq hd => ?_)
  · rw [show 33307648393 - 1 = 33307648392 from by norm_num]
    reduce_mod_char
  · have e : 33307648393 - 1 = [2 ^ 3, 3 ^ 1, 179 ^ 1, 7753177 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33307648393 - 1) / 2 = 16653824196 from by norm_num]
      have h2 : (7 : ZMod 33307648393) ^ 16653824196 = ((33307648392 : ℕ) : ZMod 33307648393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33307648393 - 1) / 3 = 11102549464 from by norm_num]
      have h2 : (7 : ZMod 33307648393) ^ 11102549464 = ((16432426456 : ℕ) : ZMod 33307648393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33307648393 - 1) / 179 = 186076248 from by norm_num]
      have h2 : (7 : ZMod 33307648393) ^ 186076248 = ((15865231472 : ℕ) : ZMod 33307648393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33307648393 - 1) / 7753177 = 4296 from by norm_num]
      have h2 : (7 : ZMod 33307648393) ^ 4296 = ((15346556379 : ℕ) : ZMod 33307648393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_238285777 : Nat.Prime 238285777 := by
  refine lucas_primality 238285777 (10 : ZMod 238285777) ?_ (fun q hq hd => ?_)
  · rw [show 238285777 - 1 = 238285776 from by norm_num]
    reduce_mod_char
  · have e : 238285777 - 1 = [2 ^ 4, 3 ^ 1, 181 ^ 1, 27427 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (238285777 - 1) / 2 = 119142888 from by norm_num]
      have h2 : (10 : ZMod 238285777) ^ 119142888 = ((238285776 : ℕ) : ZMod 238285777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (238285777 - 1) / 3 = 79428592 from by norm_num]
      have h2 : (10 : ZMod 238285777) ^ 79428592 = ((16973077 : ℕ) : ZMod 238285777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (238285777 - 1) / 181 = 1316496 from by norm_num]
      have h2 : (10 : ZMod 238285777) ^ 1316496 = ((52071165 : ℕ) : ZMod 238285777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (238285777 - 1) / 27427 = 8688 from by norm_num]
      have h2 : (10 : ZMod 238285777) ^ 8688 = ((9992771 : ℕ) : ZMod 238285777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- z = 419, e an odd multiple of 4: 3 | 145517+1, 11+1
theorem k4_419 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 8 = 4)
    (E : (2 ^ m + 1) * (1 + 419 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 419 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 419 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 419 ^ 4 ∣ 1 + 419 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g15410832361 := S7 15410832361 prime_15410832361 (by norm_num) (by decide) ((by norm_num : 15410832361 ∣ 1 + 419 ^ 4).trans hd)
  have g7705416181 := S1 7705416181 prime_7705416181 (by norm_num) (by decide) 15410832361 g15410832361 (by norm_num)
  have g3852708091 := S1 3852708091 prime_3852708091 (by norm_num) (by decide) 7705416181 g7705416181 (by norm_num)
  have g145517 := S1 145517 (by norm_num) (by norm_num) (by decide) 3852708091 g3852708091 (by norm_num)
  have g307 := S1 307 (by norm_num) (by norm_num) (by decide) 145517 g145517 (by norm_num)
  have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 307 g307 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 145517 g145517 11 g11 (by norm_num) (by norm_num)) (by norm_num)

-- z = 463, e an odd multiple of 4: 3^2 | 467+1
theorem k4_463 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 8 = 4)
    (E : (2 ^ m + 1) * (1 + 463 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 463 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 463 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 463 ^ 4 ∣ 1 + 463 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g22977034081 := S7 22977034081 prime_22977034081 (by norm_num) (by decide) ((by norm_num : 22977034081 ∣ 1 + 463 ^ 4).trans hd)
  have g11488517041 := S1 11488517041 prime_11488517041 (by norm_num) (by decide) 22977034081 g22977034081 (by norm_num)
  have g143833 := S1 143833 (by norm_num) (by norm_num) (by decide) 11488517041 g11488517041 (by norm_num)
  have g71917 := S1 71917 (by norm_num) (by norm_num) (by decide) 143833 g143833 (by norm_num)
  have g467 := S1 467 (by norm_num) (by norm_num) (by decide) 71917 g71917 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 467 g467 (by norm_num)

-- z = 503, e an odd multiple of 4: 3^2 | 291437+1
theorem k4_503 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 8 = 4)
    (E : (2 ^ m + 1) * (1 + 503 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 503 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 503 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 503 ^ 4 ∣ 1 + 503 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g32006777041 := S7 32006777041 prime_32006777041 (by norm_num) (by decide) ((by norm_num : 32006777041 ∣ 1 + 503 ^ 4).trans hd)
  have g16003388521 := S1 16003388521 prime_16003388521 (by norm_num) (by decide) 32006777041 g32006777041 (by norm_num)
  have g727426751 := S1 727426751 prime_727426751 (by norm_num) (by decide) 16003388521 g16003388521 (by norm_num)
  have g291437 := S1 291437 (by norm_num) (by norm_num) (by decide) 727426751 g727426751 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 291437 g291437 (by norm_num)

-- z = 607, e an odd multiple of 4: 3 | 137+1, 23+1
theorem k4_607 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 8 = 4)
    (E : (2 ^ m + 1) * (1 + 607 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 607 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 607 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 607 ^ 4 ∣ 1 + 607 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g67877332801 := S7 67877332801 prime_67877332801 (by norm_num) (by decide) ((by norm_num : 67877332801 ∣ 1 + 607 ^ 4).trans hd)
  have g33938666401 := S1 33938666401 prime_33938666401 (by norm_num) (by decide) 67877332801 g67877332801 (by norm_num)
  have g16969333201 := S1 16969333201 prime_16969333201 (by norm_num) (by decide) 33938666401 g33938666401 (by norm_num)
  have g137 := S1 137 (by norm_num) (by norm_num) (by decide) 16969333201 g16969333201 (by norm_num)
  have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 137 g137 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 137 g137 23 g23 (by norm_num) (by norm_num)) (by norm_num)

-- z = 883, e an odd multiple of 4: 3^2 | 14633+1
theorem k4_883 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 8 = 4)
    (E : (2 ^ m + 1) * (1 + 883 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 883 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 883 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 883 ^ 4 ∣ 1 + 883 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g303957468361 := S7 303957468361 prime_303957468361 (by norm_num) (by decide) ((by norm_num : 303957468361 ∣ 1 + 883 ^ 4).trans hd)
  have g3534389167 := S1 3534389167 prime_3534389167 (by norm_num) (by decide) 303957468361 g303957468361 (by norm_num)
  have g220899323 := S1 220899323 prime_220899323 (by norm_num) (by decide) 3534389167 g3534389167 (by norm_num)
  have g497521 := S1 497521 (by norm_num) (by norm_num) (by decide) 220899323 g220899323 (by norm_num)
  have g14633 := S1 14633 (by norm_num) (by norm_num) (by decide) 497521 g497521 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 14633 g14633 (by norm_num)

-- z = 1019, e an odd multiple of 4: 3 | 506669909+1, 16888997+1
theorem k4_1019 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 8 = 4)
    (E : (2 ^ m + 1) * (1 + 1019 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1019 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1019 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1019 ^ 4 ∣ 1 + 1019 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g539096783161 := S7 539096783161 prime_539096783161 (by norm_num) (by decide) ((by norm_num : 539096783161 ∣ 1 + 1019 ^ 4).trans hd)
  have g38506913083 := S1 38506913083 prime_38506913083 (by norm_num) (by decide) 539096783161 g539096783161 (by norm_num)
  have g506669909 := S1 506669909 prime_506669909 (by norm_num) (by decide) 38506913083 g38506913083 (by norm_num)
  have g16888997 := S1 16888997 (by norm_num) (by norm_num) (by decide) 506669909 g506669909 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 506669909 g506669909 16888997 g16888997 (by norm_num) (by norm_num)) (by norm_num)

-- z = 1327, e an odd multiple of 4: 3^2 | 432599183+1
theorem k4_1327 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 8 = 4)
    (E : (2 ^ m + 1) * (1 + 1327 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1327 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1327 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1327 ^ 4 ∣ 1 + 1327 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g1550435471521 := S7 1550435471521 prime_1550435471521 (by norm_num) (by decide) ((by norm_num : 1550435471521 ∣ 1 + 1327 ^ 4).trans hd)
  have g110745390823 := S1 110745390823 prime_110745390823 (by norm_num) (by decide) 1550435471521 g1550435471521 (by norm_num)
  have g13843173853 := S1 13843173853 prime_13843173853 (by norm_num) (by decide) 110745390823 g110745390823 (by norm_num)
  have g6921586927 := S1 6921586927 prime_6921586927 (by norm_num) (by decide) 13843173853 g13843173853 (by norm_num)
  have g432599183 := S1 432599183 prime_432599183 (by norm_num) (by decide) 6921586927 g6921586927 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 432599183 g432599183 (by norm_num)

-- z = 11, e an odd multiple of 12: 73^2 | 10657+1
theorem k11_3 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 24 = 12)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 12 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g10657 := S7 10657 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10657 ∣ 1 + 11 ^ 12).trans hd)
  exact S6 73 (by norm_num) (by norm_num) (by decide) 10657 g10657 (by norm_num)

-- z = 11, e an odd multiple of 20: 7 | 41+1, 7321+1
theorem k11_5 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 40 = 20)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 20 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g41 := S7 41 (by norm_num) (by norm_num) (by decide) ((by norm_num : 41 ∣ 1 + 11 ^ 20).trans hd)
  have g7321 := S7 7321 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7321 ∣ 1 + 11 ^ 20).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 41 g41 7321 g7321 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 28: 3^2 | 449+1
theorem k11_7 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 56 = 28)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 28 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 11 ^ 28).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)

-- z = 11, e an odd multiple of 44: 3 | 353+1, 59+1
theorem k11_11 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 88 = 44)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 44 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g353 := S7 353 (by norm_num) (by norm_num) (by decide) ((by norm_num : 353 ∣ 1 + 11 ^ 44).trans hd)
  have g59 := S1 59 (by norm_num) (by norm_num) (by decide) 353 g353 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 353 g353 59 g59 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 52: 3 | 23+1, 131+1
theorem k11_13 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 104 = 52)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 52 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g97010607829826070873559937268360584022789501553441 := S7 97010607829826070873559937268360584022789501553441 prime_97010607829826070873559937268360584022789501553441 (by norm_num) (by decide) ((by norm_num : 97010607829826070873559937268360584022789501553441 ∣ 1 + 11 ^ 52).trans hd)
  have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 97010607829826070873559937268360584022789501553441 g97010607829826070873559937268360584022789501553441 (by norm_num)
  have g7321 := S7 7321 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7321 ∣ 1 + 11 ^ 52).trans hd)
  have g523 := S1 523 (by norm_num) (by norm_num) (by decide) 7321 g7321 (by norm_num)
  have g131 := S1 131 (by norm_num) (by norm_num) (by decide) 523 g523 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 23 g23 131 g131 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 68: 3^2 | 11969+1
theorem k11_17 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 136 = 68)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 68 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g11969 := S7 11969 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11969 ∣ 1 + 11 ^ 68).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 11969 g11969 (by norm_num)

-- z = 11, e an odd multiple of 76: 3^2 | 701+1
theorem k11_19 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 152 = 76)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 76 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g35613601 := S7 35613601 (by norm_num) (by norm_num) (by decide) ((by norm_num : 35613601 ∣ 1 + 11 ^ 76).trans hd)
  have g17806801 := S1 17806801 (by norm_num) (by norm_num) (by decide) 35613601 g35613601 (by norm_num)
  have g701 := S1 701 (by norm_num) (by norm_num) (by decide) 17806801 g17806801 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 701 g701 (by norm_num)

-- z = 11, e an odd multiple of 92: 3 | 34961+1, 47+1
theorem k11_23 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 184 = 92)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 92 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g34961 := S7 34961 (by norm_num) (by norm_num) (by decide) ((by norm_num : 34961 ∣ 1 + 11 ^ 92).trans hd)
  have g5827 := S1 5827 (by norm_num) (by norm_num) (by decide) 34961 g34961 (by norm_num)
  have g47 := S1 47 (by norm_num) (by norm_num) (by decide) 5827 g5827 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 34961 g34961 47 g47 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 116: 3^2 | 233+1
theorem k11_29 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 232 = 116)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 116 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g233 := S7 233 (by norm_num) (by norm_num) (by decide) ((by norm_num : 233 ∣ 1 + 11 ^ 116).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 233 g233 (by norm_num)

-- z = 11, e an odd multiple of 124: 5^2 | 6449+1
theorem k11_31 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 248 = 124)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 124 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g6449 := S7 6449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6449 ∣ 1 + 11 ^ 124).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (by decide) 6449 g6449 (by norm_num)

-- z = 11, e an odd multiple of 148: 3 | 1481+1, 5+1
theorem k11_37 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 296 = 148)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 148 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g1481 := S7 1481 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1481 ∣ 1 + 11 ^ 148).trans hd)
  have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 1481 g1481 (by norm_num)
  have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1481 g1481 5 g5 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 164: 3^2 | 13121+1
theorem k11_41 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 328 = 164)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 164 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g13121 := S7 13121 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13121 ∣ 1 + 11 ^ 164).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 13121 g13121 (by norm_num)

-- z = 11, e an odd multiple of 172: 13 | 10321+1, 895777+1
theorem k11_43 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 344 = 172)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 172 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g10321 := S7 10321 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10321 ∣ 1 + 11 ^ 172).trans hd)
  have g895777 := S7 895777 (by norm_num) (by norm_num) (by decide) ((by norm_num : 895777 ∣ 1 + 11 ^ 172).trans hd)
  exact absurd (S3 13 (by norm_num) (by norm_num) (by decide) 10321 g10321 895777 g895777 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 188: 5^2 | 23549+1
theorem k11_47 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 376 = 188)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 188 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g149441953 := S7 149441953 prime_149441953 (by norm_num) (by decide) ((by norm_num : 149441953 ∣ 1 + 11 ^ 188).trans hd)
  have g23549 := S1 23549 (by norm_num) (by norm_num) (by decide) 149441953 g149441953 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (by decide) 23549 g23549 (by norm_num)

-- z = 11, e an odd multiple of 212: 5 | 20346651139084609+1, 59+1
theorem k11_53 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 424 = 212)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 212 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g20346651139084609 := S7 20346651139084609 prime_20346651139084609 (by norm_num) (by decide) ((by norm_num : 20346651139084609 ∣ 1 + 11 ^ 212).trans hd)
  have g59 := S1 59 (by norm_num) (by norm_num) (by decide) 20346651139084609 g20346651139084609 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 20346651139084609 g20346651139084609 59 g59 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 236: 3 | 1245137+1, 29+1
theorem k11_59 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 472 = 236)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 236 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g1245137 := S7 1245137 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1245137 ∣ 1 + 11 ^ 236).trans hd)
  have g207523 := S1 207523 (by norm_num) (by norm_num) (by decide) 1245137 g1245137 (by norm_num)
  have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 207523 g207523 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1245137 g1245137 29 g29 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 244: 3 | 977+1, 41+1
theorem k11_61 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 488 = 244)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 244 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g977 := S7 977 (by norm_num) (by norm_num) (by decide) ((by norm_num : 977 ∣ 1 + 11 ^ 244).trans hd)
  have g163 := S1 163 (by norm_num) (by norm_num) (by decide) 977 g977 (by norm_num)
  have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 163 g163 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 977 g977 41 g41 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 268: 3^2 | 17+1
theorem k11_67 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 536 = 268)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 268 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g13301377 := S7 13301377 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 268 = 11 ^ 200 * 11 ^ 68 by rw [← pow_add]]; norm_num : 13301377 ∣ 1 + 11 ^ 268).trans hd)
  have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 13301377 g13301377 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)

-- z = 11, e an odd multiple of 284: 3 | 569+1, 12497+1
theorem k11_71 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 568 = 284)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 284 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g569 := S7 569 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 284 = 11 ^ 200 * 11 ^ 84 by rw [← pow_add]]; norm_num : 569 ∣ 1 + 11 ^ 284).trans hd)
  have g12497 := S7 12497 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 284 = 11 ^ 200 * 11 ^ 84 by rw [← pow_add]]; norm_num : 12497 ∣ 1 + 11 ^ 284).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 569 g569 12497 g12497 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 292: 3 | 4673+1, 41+1
theorem k11_73 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 584 = 292)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 292 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g4673 := S7 4673 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 292 = 11 ^ 200 * 11 ^ 92 by rw [← pow_add]]; norm_num : 4673 ∣ 1 + 11 ^ 292).trans hd)
  have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 4673 g4673 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 4673 g4673 41 g41 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 316: 5^2 | 77549+1
theorem k11_79 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 632 = 316)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 316 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g117567026551063291227924640993 := S7 117567026551063291227924640993 prime_117567026551063291227924640993 (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 316 = 11 ^ 200 * 11 ^ 116 by rw [← pow_add]]; norm_num : 117567026551063291227924640993 ∣ 1 + 11 ^ 316).trans hd)
  have g77549 := S1 77549 (by norm_num) (by norm_num) (by decide) 117567026551063291227924640993 g117567026551063291227924640993 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (by decide) 77549 g77549 (by norm_num)

-- z = 11, e an odd multiple of 332: 5^2 | 499+1
theorem k11_83 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 664 = 332)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 332 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g1993 := S7 1993 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 332 = 11 ^ 200 * 11 ^ 132 by rw [← pow_add]]; norm_num : 1993 ∣ 1 + 11 ^ 332).trans hd)
  have g997 := S1 997 (by norm_num) (by norm_num) (by decide) 1993 g1993 (by norm_num)
  have g499 := S1 499 (by norm_num) (by norm_num) (by decide) 997 g997 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (by decide) 499 g499 (by norm_num)

-- z = 11, e an odd multiple of 356: 3^2 | 11321+1
theorem k11_89 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 712 = 356)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 356 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g113209 := S7 113209 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 356 = 11 ^ 200 * 11 ^ 156 by rw [← pow_add]]; norm_num : 113209 ∣ 1 + 11 ^ 356).trans hd)
  have g11321 := S1 11321 (by norm_num) (by norm_num) (by decide) 113209 g113209 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 11321 g11321 (by norm_num)

-- z = 11, e an odd multiple of 388: 7 | 7321+1, 335786251793+1
theorem k11_97 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 776 = 388)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 388 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g7321 := S7 7321 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 388 = 11 ^ 200 * 11 ^ 188 by rw [← pow_add]]; norm_num : 7321 ∣ 1 + 11 ^ 388).trans hd)
  have g335786251793 := S7 335786251793 prime_335786251793 (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 388 = 11 ^ 200 * 11 ^ 188 by rw [← pow_add]]; norm_num : 335786251793 ∣ 1 + 11 ^ 388).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 7321 g7321 335786251793 g335786251793 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 404: 3^2 | 809+1
theorem k11_101 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 808 = 404)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 404 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g809 := S7 809 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 404 = 11 ^ 200 * (11 ^ 200 * 11 ^ 4) by rw [← pow_add, ← pow_add]]; norm_num : 809 ∣ 1 + 11 ^ 404).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 809 g809 (by norm_num)

-- z = 11, e an odd multiple of 412: 5^2 | 62327847687645911640969067843358449+1
theorem k11_103 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 824 = 412)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 412 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g62327847687645911640969067843358449 := S7 62327847687645911640969067843358449 prime_62327847687645911640969067843358449 (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 412 = 11 ^ 200 * (11 ^ 200 * 11 ^ 12) by rw [← pow_add, ← pow_add]]; norm_num : 62327847687645911640969067843358449 ∣ 1 + 11 ^ 412).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (by decide) 62327847687645911640969067843358449 g62327847687645911640969067843358449 (by norm_num)

-- z = 11, e an odd multiple of 428: 3^2 | 71+1
theorem k11_107 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 856 = 428)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 428 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g1002377 := S7 1002377 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 428 = 11 ^ 200 * (11 ^ 200 * 11 ^ 28) by rw [← pow_add, ← pow_add]]; norm_num : 1002377 ∣ 1 + 11 ^ 428).trans hd)
  have g71 := S1 71 (by norm_num) (by norm_num) (by decide) 1002377 g1002377 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)

-- z = 11, e an odd multiple of 436: 3^2 | 17+1
theorem k11_109 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 872 = 436)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 436 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g2617 := S7 2617 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 436 = 11 ^ 200 * (11 ^ 200 * 11 ^ 36) by rw [← pow_add, ← pow_add]]; norm_num : 2617 ∣ 1 + 11 ^ 436).trans hd)
  have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 2617 g2617 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)

-- z = 11, e an odd multiple of 508: 3^2 | 56897+1
theorem k11_127 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1016 = 508)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 508 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g56897 := S7 56897 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 508 = 11 ^ 200 * (11 ^ 200 * 11 ^ 108) by rw [← pow_add, ← pow_add]]; norm_num : 56897 ∣ 1 + 11 ^ 508).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 56897 g56897 (by norm_num)

-- z = 11, e an odd multiple of 524: 3^2 | 23057+1
theorem k11_131 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1048 = 524)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 524 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g23057 := S7 23057 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 524 = 11 ^ 200 * (11 ^ 200 * 11 ^ 124) by rw [← pow_add, ← pow_add]]; norm_num : 23057 ∣ 1 + 11 ^ 524).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 23057 g23057 (by norm_num)

-- z = 11, e an odd multiple of 548: 3^2 | 1097+1
theorem k11_137 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1096 = 548)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 548 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g1097 := S7 1097 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 548 = 11 ^ 200 * (11 ^ 200 * 11 ^ 148) by rw [← pow_add, ← pow_add]]; norm_num : 1097 ∣ 1 + 11 ^ 548).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 1097 g1097 (by norm_num)

-- z = 11, e an odd multiple of 556: 3 | 1436269938872009+1, 5+1
theorem k11_139 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1112 = 556)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 556 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g1436269938872009 := S7 1436269938872009 prime_1436269938872009 (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 556 = 11 ^ 200 * (11 ^ 200 * 11 ^ 156) by rw [← pow_add, ← pow_add]]; norm_num : 1436269938872009 ∣ 1 + 11 ^ 556).trans hd)
  have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 1436269938872009 g1436269938872009 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1436269938872009 g1436269938872009 5 g5 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 604: 3^2 | 216233+1
theorem k11_151 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1208 = 604)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 604 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g216233 := S7 216233 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 604 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 4)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 216233 ∣ 1 + 11 ^ 604).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 216233 g216233 (by norm_num)

-- z = 11, e an odd multiple of 628: 3^2 | 107+1
theorem k11_157 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1256 = 628)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 628 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g42232714889 := S7 42232714889 prime_42232714889 (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 628 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 28)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 42232714889 ∣ 1 + 11 ^ 628).trans hd)
  have g107 := S1 107 (by norm_num) (by norm_num) (by decide) 42232714889 g42232714889 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)

-- z = 11, e an odd multiple of 652: 3 | 10433+1, 47+1
theorem k11_163 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1304 = 652)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 652 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g10433 := S7 10433 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 652 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 52)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 10433 ∣ 1 + 11 ^ 652).trans hd)
  have g47 := S1 47 (by norm_num) (by norm_num) (by decide) 10433 g10433 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 10433 g10433 47 g47 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 668: 3^2 | 179+1
theorem k11_167 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1336 = 668)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 668 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g184369 := S7 184369 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 668 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 68)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 184369 ∣ 1 + 11 ^ 668).trans hd)
  have g179 := S1 179 (by norm_num) (by norm_num) (by decide) 184369 g184369 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 179 g179 (by norm_num)

-- z = 11, e an odd multiple of 692: 3^2 | 13841+1
theorem k11_173 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1384 = 692)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 692 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g13841 := S7 13841 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 692 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 92)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 13841 ∣ 1 + 11 ^ 692).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 13841 g13841 (by norm_num)

-- z = 11, e an odd multiple of 716: 19^2 | 33307648393+1
theorem k11_179 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1432 = 716)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 716 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g33307648393 := S7 33307648393 prime_33307648393 (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 716 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 116)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 33307648393 ∣ 1 + 11 ^ 716).trans hd)
  exact S6 19 (by norm_num) (by norm_num) (by decide) 33307648393 g33307648393 (by norm_num)

-- z = 11, e an odd multiple of 724: 3^2 | 65141+1
theorem k11_181 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1448 = 724)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 724 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g238285777 := S7 238285777 prime_238285777 (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 724 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 124)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 238285777 ∣ 1 + 11 ^ 724).trans hd)
  have g65141 := S1 65141 (by norm_num) (by norm_num) (by decide) 238285777 g238285777 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 65141 g65141 (by norm_num)

-- z = 11, e an odd multiple of 764: 5 | 32089+1, 3209+1
theorem k11_191 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1528 = 764)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 764 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g32089 := S7 32089 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 764 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 164)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 32089 ∣ 1 + 11 ^ 764).trans hd)
  have g3209 := S1 3209 (by norm_num) (by norm_num) (by decide) 32089 g32089 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 32089 g32089 3209 g3209 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 772: 3 | 3089+1, 5+1
theorem k11_193 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1544 = 772)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 772 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g3089 := S7 3089 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 772 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 172)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 3089 ∣ 1 + 11 ^ 772).trans hd)
  have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 3089 g3089 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 3089 g3089 5 g5 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 788: 3^2 | 71+1
theorem k11_197 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1576 = 788)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 788 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g15761 := S7 15761 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 788 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 188)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 15761 ∣ 1 + 11 ^ 788).trans hd)
  have g71 := S1 71 (by norm_num) (by norm_num) (by decide) 15761 g15761 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)

-- z = 11, e an odd multiple of 796: 3^2 | 251+1
theorem k11_199 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1592 = 796)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 796 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g55721 := S7 55721 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 796 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 196)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 55721 ∣ 1 + 11 ^ 796).trans hd)
  have g251 := S1 251 (by norm_num) (by norm_num) (by decide) 55721 g55721 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 251 g251 (by norm_num)

-- z = 11, e an odd multiple of 892: 3^2 | 817073+1
theorem k11_223 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1784 = 892)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 892 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g817073 := S7 817073 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 892 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 92))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 817073 ∣ 1 + 11 ^ 892).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 817073 g817073 (by norm_num)

-- z = 11, e an odd multiple of 908: 3^2 | 2447+1
theorem k11_227 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1816 = 908)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 908 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g17324641 := S7 17324641 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 908 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 108))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 17324641 ∣ 1 + 11 ^ 908).trans hd)
  have g146819 := S1 146819 (by norm_num) (by norm_num) (by decide) 17324641 g17324641 (by norm_num)
  have g2447 := S1 2447 (by norm_num) (by norm_num) (by decide) 146819 g146819 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 2447 g2447 (by norm_num)

-- z = 11, e an odd multiple of 932: 7 | 7321+1, 807113+1
theorem k11_233 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1864 = 932)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 932 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g7321 := S7 7321 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 932 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 132))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 7321 ∣ 1 + 11 ^ 932).trans hd)
  have g807113 := S7 807113 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 932 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 132))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 807113 ∣ 1 + 11 ^ 932).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 7321 g7321 807113 g807113 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 956: 3 | 1913+1, 29+1
theorem k11_239 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1912 = 956)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 956 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g1913 := S7 1913 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 956 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 156))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 1913 ∣ 1 + 11 ^ 956).trans hd)
  have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 1913 g1913 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1913 g1913 29 g29 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 964: 3^2 | 4157+1
theorem k11_241 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 1928 = 964)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 964 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g1970417 := S7 1970417 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 964 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 164))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 1970417 ∣ 1 + 11 ^ 964).trans hd)
  have g4157 := S1 4157 (by norm_num) (by norm_num) (by decide) 1970417 g1970417 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 4157 g4157 (by norm_num)

-- z = 11, e an odd multiple of 1076: 3^2 | 359+1
theorem k11_269 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 2152 = 1076)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 1076 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g2153 := S7 2153 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 1076 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 76)))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 2153 ∣ 1 + 11 ^ 1076).trans hd)
  have g359 := S1 359 (by norm_num) (by norm_num) (by decide) 2153 g2153 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 359 g359 (by norm_num)

-- z = 11, e an odd multiple of 1084: 5^2 | 79549+1
theorem k11_271 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 2168 = 1084)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 1084 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g2068273 := S7 2068273 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 1084 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 84)))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 2068273 ∣ 1 + 11 ^ 1084).trans hd)
  have g79549 := S1 79549 (by norm_num) (by norm_num) (by decide) 2068273 g2068273 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (by decide) 79549 g79549 (by norm_num)

-- z = 11, e an odd multiple of 1124: 5 | 18593209+1, 19+1
theorem k11_281 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 2248 = 1124)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 1124 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g18593209 := S7 18593209 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 1124 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 124)))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 18593209 ∣ 1 + 11 ^ 1124).trans hd)
  have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 18593209 g18593209 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 18593209 g18593209 19 g19 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 1132: 3^2 | 378089+1
theorem k11_283 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 2264 = 1132)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 1132 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g378089 := S7 378089 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 1132 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 132)))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 378089 ∣ 1 + 11 ^ 1132).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 378089 g378089 (by norm_num)

-- z = 11, e an odd multiple of 1172: 3 | 5+1, 383+1
theorem k11_293 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 2344 = 1172)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 1172 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g3473809 := S7 3473809 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 1172 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 172)))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 3473809 ∣ 1 + 11 ^ 1172).trans hd)
  have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 3473809 g3473809 (by norm_num)
  have g383 := S1 383 (by norm_num) (by norm_num) (by decide) 3473809 g3473809 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 383 g383 (by norm_num) (by norm_num)) (by norm_num)

-- z = 11, e an odd multiple of 1228: 3^2 | 93329+1
theorem k11_307 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 2456 = 1228)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 1228 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g93329 := S7 93329 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 1228 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 28))))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 93329 ∣ 1 + 11 ^ 1228).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 93329 g93329 (by norm_num)

-- z = 11, e an odd multiple of 1348: 3^2 | 719+1
theorem k11_337 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 2696 = 1348)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 1348 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g21569 := S7 21569 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 1348 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 148))))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 21569 ∣ 1 + 11 ^ 1348).trans hd)
  have g719 := S1 719 (by norm_num) (by norm_num) (by decide) 21569 g21569 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 719 g719 (by norm_num)

-- z = 11, e an odd multiple of 1436: 7^2 | 97+1
theorem k11_359 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 2872 = 1436)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 1436 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g16870129 := S7 16870129 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 1436 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 36)))))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 16870129 ∣ 1 + 11 ^ 1436).trans hd)
  have g193 := S1 193 (by norm_num) (by norm_num) (by decide) 16870129 g16870129 (by norm_num)
  have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)

-- z = 11, e an odd multiple of 1468: 3^2 | 2322377+1
theorem k11_367 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 2936 = 1468)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 1468 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g2322377 := S7 2322377 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 1468 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 68)))))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 2322377 ∣ 1 + 11 ^ 1468).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 2322377 g2322377 (by norm_num)

-- z = 11, e an odd multiple of 1492: 3^2 | 3581+1
theorem k11_373 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 2984 = 1492)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 11 ^ 1492 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g35809 := S7 35809 (by norm_num) (by norm_num) (by decide) ((by rw [show (11:ℕ) ^ 1492 = 11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * (11 ^ 200 * 11 ^ 92)))))) by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 35809 ∣ 1 + 11 ^ 1492).trans hd)
  have g3581 := S1 3581 (by norm_num) (by norm_num) (by decide) 35809 g35809 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 3581 g3581 (by norm_num)

-- The sieve of e for z = 11.
set_option maxHeartbeats 4000000 in
theorem esieve11 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 8 = 4)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) :
    ∀ k ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
      101, 103, 107, 109, 127, 131, 137, 139, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197,
      199, 223, 227, 233, 239, 241, 269, 271, 281, 283, 293, 307, 337, 359, 367, 373} : Finset ℕ),
      ¬ k ∣ e := by
  intro k hk hdv
  obtain ⟨t, ht⟩ := hdv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact k11_3 hP (by omega) E
  · exact k11_5 hP (by omega) E
  · exact k11_7 hP (by omega) E
  · exact k11_11 hP (by omega) E
  · exact k11_13 hP (by omega) E
  · exact k11_17 hP (by omega) E
  · exact k11_19 hP (by omega) E
  · exact k11_23 hP (by omega) E
  · exact k11_29 hP (by omega) E
  · exact k11_31 hP (by omega) E
  · exact k11_37 hP (by omega) E
  · exact k11_41 hP (by omega) E
  · exact k11_43 hP (by omega) E
  · exact k11_47 hP (by omega) E
  · exact k11_53 hP (by omega) E
  · exact k11_59 hP (by omega) E
  · exact k11_61 hP (by omega) E
  · exact k11_67 hP (by omega) E
  · exact k11_71 hP (by omega) E
  · exact k11_73 hP (by omega) E
  · exact k11_79 hP (by omega) E
  · exact k11_83 hP (by omega) E
  · exact k11_89 hP (by omega) E
  · exact k11_97 hP (by omega) E
  · exact k11_101 hP (by omega) E
  · exact k11_103 hP (by omega) E
  · exact k11_107 hP (by omega) E
  · exact k11_109 hP (by omega) E
  · exact k11_127 hP (by omega) E
  · exact k11_131 hP (by omega) E
  · exact k11_137 hP (by omega) E
  · exact k11_139 hP (by omega) E
  · exact k11_151 hP (by omega) E
  · exact k11_157 hP (by omega) E
  · exact k11_163 hP (by omega) E
  · exact k11_167 hP (by omega) E
  · exact k11_173 hP (by omega) E
  · exact k11_179 hP (by omega) E
  · exact k11_181 hP (by omega) E
  · exact k11_191 hP (by omega) E
  · exact k11_193 hP (by omega) E
  · exact k11_197 hP (by omega) E
  · exact k11_199 hP (by omega) E
  · exact k11_223 hP (by omega) E
  · exact k11_227 hP (by omega) E
  · exact k11_233 hP (by omega) E
  · exact k11_239 hP (by omega) E
  · exact k11_241 hP (by omega) E
  · exact k11_269 hP (by omega) E
  · exact k11_271 hP (by omega) E
  · exact k11_281 hP (by omega) E
  · exact k11_283 hP (by omega) E
  · exact k11_293 hP (by omega) E
  · exact k11_307 hP (by omega) E
  · exact k11_337 hP (by omega) E
  · exact k11_359 hP (by omega) E
  · exact k11_367 hP (by omega) E
  · exact k11_373 hP (by omega) E

-- Section 2. The step.
theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1.H3 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max A1 A2, fun n h z hz hS c hm c0 _ _ c4 c5 c6 _ c15 U R => ?_⟩
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hz2 : z ≠ 2 := by omega
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have U' : Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ 11 ∣ 2 ^ d + 1 :=
      fun ha d hd => (U ha d hd).imp id And.right
    rcases Nat.lt_or_ge 4 (n.factorization 11) with h4 | h4
    · exact (h2 n h hS c h4 (esieve11 hP c E) c0 c4 (c5 (by norm_num)) (c6 (by norm_num))
        (c15 (by norm_num)) U' R).trans (le_max_right _ _)
    · exact (h1 n h hS (by omega) c0 c4 (c5 (by norm_num)) (c6 (by norm_num))
        (c15 (by norm_num)) U' R).trans (le_max_left _ _)
  · exact (k4_419 hP c E).elim
  · exact (k4_463 hP c E).elim
  · exact (k4_503 hP c E).elim
  · exact (k4_607 hP c E).elim
  · exact (k4_883 hP c E).elim
  · exact (k4_1019 hP c E).elim
  · exact (k4_1327 hP c E).elim

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H3_R1
