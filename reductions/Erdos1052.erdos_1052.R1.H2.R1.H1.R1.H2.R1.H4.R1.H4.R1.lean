import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1
-- Upstream path: reductions/Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1.lean
-- Credit: @adammcarter (agent: Claude Code, model claude-fable-5-2)
--
-- Splits step H4 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1 (the unitary perfect number n has exactly one
-- repeated odd prime z, 7 <= z < 2100, exponent e = v_z(n) divisible by 8, a = padicValNat 2 n)
-- by e mod 32, after sieving the prime z in the classes e = 8 mod 16 and e = 16 mod 32.
-- Proving H1 and H2 proves the step.
--
-- Notation as in the parent file: P = the set of simple odd primes of n.  The balance equation is
--   (2^a + 1)(1 + z^e) prod_P (p + 1) = 2^(a+1) z^e prod_P p,
-- in which every odd prime other than z occurs exactly once on the left.  If e = 8 mod 16 then
-- z^8 + 1 divides 1 + z^e; if e = 16 mod 32 then z^16 + 1 does.  Their odd primes are simple
-- primes of n, and the odd primes (other than z) of p + 1 for simple p are simple again.
--
-- PROVED BELOW (no hypothesis needed), zsieve (there are 314 primes z in [7, 2100)):
--  * e = 8 mod 16 is impossible.  For every z other than 7 the forced chain from z^8 + 1 ends in a
--    contradiction: an odd square divides z^8 + 1 (12 primes z), a square divides some p + 1
--    (262), or a prime has two sources on the left (39).  For z = 7 the parent step already
--    assumes e mod 16 is not 8.  So 16 divides e.
--  * e = 16 mod 32: z is one of 31 primes (282 excluded from z^16 + 1: 1, 206 and 75 cases; z = 7
--    excluded by the parent's condition on e).
--  Primes above 4.3 * 10^7 on the chains carry a Lucas certificate (theorems prime_<p>, 112 new,
--  up to 27 digits).
--
-- H1 (OPEN): e = 16 mod 32, z in the list of 31.  These are left only for file size: each
--   needs one or two more large certificates.
-- H2 (OPEN): 32 divides e.
-- Each H keeps the conditions of the parent step on a.
-- No known unitary perfect number has a repeated odd prime z >= 7.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1 hiding H1 H2 H3 H4 main

-- H1: a is bounded when e = 16 mod 32.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 32 = 16 →
    z ∈ ({41, 73, 113, 157, 167, 173, 199, 307, 449, 599, 607, 617, 643, 743, 811, 937, 967, 1201,
      1213, 1237, 1249, 1277, 1297, 1373, 1579, 1637, 1667, 1747, 1979, 2011, 2027} : Finset ℕ) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1)) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- H2: a is bounded when 32 divides e.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime → 7 ≤ z → z < 2100 →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 32 = 0 →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1)) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- Section 1. Lucas certificates and the sieve of z, in ranges of 300.

theorem prime_407865361 : Nat.Prime 407865361 := by
  refine lucas_primality 407865361 (11 : ZMod 407865361) ?_ (fun q hq hd => ?_)
  · rw [show 407865361 - 1 = 407865360 from by norm_num]
    reduce_mod_char
  · have e : 407865361 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 14281 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (407865361 - 1) / 2 = 203932680 from by norm_num]
      have h2 : (11 : ZMod 407865361) ^ 203932680 = ((407865360 : ℕ) : ZMod 407865361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (407865361 - 1) / 3 = 135955120 from by norm_num]
      have h2 : (11 : ZMod 407865361) ^ 135955120 = ((388788868 : ℕ) : ZMod 407865361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (407865361 - 1) / 5 = 81573072 from by norm_num]
      have h2 : (11 : ZMod 407865361) ^ 81573072 = ((300398511 : ℕ) : ZMod 407865361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (407865361 - 1) / 7 = 58266480 from by norm_num]
      have h2 : (11 : ZMod 407865361) ^ 58266480 = ((330426176 : ℕ) : ZMod 407865361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (407865361 - 1) / 17 = 23992080 from by norm_num]
      have h2 : (11 : ZMod 407865361) ^ 23992080 = ((49842018 : ℕ) : ZMod 407865361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (407865361 - 1) / 14281 = 28560 from by norm_num]
      have h2 : (11 : ZMod 407865361) ^ 28560 = ((2963373 : ℕ) : ZMod 407865361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5844100138801 : Nat.Prime 5844100138801 := by
  refine lucas_primality 5844100138801 (39 : ZMod 5844100138801) ?_ (fun q hq hd => ?_)
  · rw [show 5844100138801 - 1 = 5844100138800 from by norm_num]
    reduce_mod_char
  · have e : 5844100138801 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 2, 7 ^ 1, 11 ^ 1, 17 ^ 1, 37 ^ 1, 193 ^ 1, 521 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5844100138801 - 1) / 2 = 2922050069400 from by norm_num]
      have h2 : (39 : ZMod 5844100138801) ^ 2922050069400 = ((5844100138800 : ℕ) : ZMod 5844100138801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5844100138801 - 1) / 3 = 1948033379600 from by norm_num]
      have h2 : (39 : ZMod 5844100138801) ^ 1948033379600 = ((3898849014355 : ℕ) : ZMod 5844100138801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5844100138801 - 1) / 5 = 1168820027760 from by norm_num]
      have h2 : (39 : ZMod 5844100138801) ^ 1168820027760 = ((168710660029 : ℕ) : ZMod 5844100138801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5844100138801 - 1) / 7 = 834871448400 from by norm_num]
      have h2 : (39 : ZMod 5844100138801) ^ 834871448400 = ((2313013398304 : ℕ) : ZMod 5844100138801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5844100138801 - 1) / 11 = 531281830800 from by norm_num]
      have h2 : (39 : ZMod 5844100138801) ^ 531281830800 = ((4031245820467 : ℕ) : ZMod 5844100138801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5844100138801 - 1) / 17 = 343770596400 from by norm_num]
      have h2 : (39 : ZMod 5844100138801) ^ 343770596400 = ((1504211832417 : ℕ) : ZMod 5844100138801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5844100138801 - 1) / 37 = 157948652400 from by norm_num]
      have h2 : (39 : ZMod 5844100138801) ^ 157948652400 = ((193587787826 : ℕ) : ZMod 5844100138801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5844100138801 - 1) / 193 = 30280311600 from by norm_num]
      have h2 : (39 : ZMod 5844100138801) ^ 30280311600 = ((1351442645499 : ℕ) : ZMod 5844100138801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5844100138801 - 1) / 521 = 11217082800 from by norm_num]
      have h2 : (39 : ZMod 5844100138801) ^ 11217082800 = ((532261738868 : ℕ) : ZMod 5844100138801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11905643330881 : Nat.Prime 11905643330881 := by
  refine lucas_primality 11905643330881 (7 : ZMod 11905643330881) ?_ (fun q hq hd => ?_)
  · rw [show 11905643330881 - 1 = 11905643330880 from by norm_num]
    reduce_mod_char
  · have e : 11905643330881 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 13 ^ 1, 17 ^ 1, 23 ^ 1, 97 ^ 1, 25153 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11905643330881 - 1) / 2 = 5952821665440 from by norm_num]
      have h2 : (7 : ZMod 11905643330881) ^ 5952821665440 = ((11905643330880 : ℕ) : ZMod 11905643330881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11905643330881 - 1) / 3 = 3968547776960 from by norm_num]
      have h2 : (7 : ZMod 11905643330881) ^ 3968547776960 = ((3343525563345 : ℕ) : ZMod 11905643330881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11905643330881 - 1) / 5 = 2381128666176 from by norm_num]
      have h2 : (7 : ZMod 11905643330881) ^ 2381128666176 = ((1454908708599 : ℕ) : ZMod 11905643330881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11905643330881 - 1) / 13 = 915818717760 from by norm_num]
      have h2 : (7 : ZMod 11905643330881) ^ 915818717760 = ((737212015541 : ℕ) : ZMod 11905643330881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11905643330881 - 1) / 17 = 700331960640 from by norm_num]
      have h2 : (7 : ZMod 11905643330881) ^ 700331960640 = ((10685140722960 : ℕ) : ZMod 11905643330881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11905643330881 - 1) / 23 = 517636666560 from by norm_num]
      have h2 : (7 : ZMod 11905643330881) ^ 517636666560 = ((1278383570980 : ℕ) : ZMod 11905643330881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11905643330881 - 1) / 97 = 122738591040 from by norm_num]
      have h2 : (7 : ZMod 11905643330881) ^ 122738591040 = ((7529943984381 : ℕ) : ZMod 11905643330881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11905643330881 - 1) / 25153 = 473328960 from by norm_num]
      have h2 : (7 : ZMod 11905643330881) ^ 473328960 = ((8473149679318 : ℕ) : ZMod 11905643330881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_850403095063 : Nat.Prime 850403095063 := by
  refine lucas_primality 850403095063 (3 : ZMod 850403095063) ?_ (fun q hq hd => ?_)
  · rw [show 850403095063 - 1 = 850403095062 from by norm_num]
    reduce_mod_char
  · have e : 850403095063 - 1 = [2 ^ 1, 3 ^ 1, 223 ^ 1, 521 ^ 1, 1219919 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (850403095063 - 1) / 2 = 425201547531 from by norm_num]
      have h2 : (3 : ZMod 850403095063) ^ 425201547531 = ((850403095062 : ℕ) : ZMod 850403095063) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (850403095063 - 1) / 3 = 283467698354 from by norm_num]
      have h2 : (3 : ZMod 850403095063) ^ 283467698354 = ((850400655222 : ℕ) : ZMod 850403095063) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (850403095063 - 1) / 223 = 3813466794 from by norm_num]
      have h2 : (3 : ZMod 850403095063) ^ 3813466794 = ((162729766144 : ℕ) : ZMod 850403095063) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (850403095063 - 1) / 521 = 1632251622 from by norm_num]
      have h2 : (3 : ZMod 850403095063) ^ 1632251622 = ((107746802891 : ℕ) : ZMod 850403095063) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (850403095063 - 1) / 1219919 = 697098 from by norm_num]
      have h2 : (3 : ZMod 850403095063) ^ 697098 = ((217925314960 : ℕ) : ZMod 850403095063) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_31129845205681 : Nat.Prime 31129845205681 := by
  refine lucas_primality 31129845205681 (19 : ZMod 31129845205681) ?_ (fun q hq hd => ?_)
  · rw [show 31129845205681 - 1 = 31129845205680 from by norm_num]
    reduce_mod_char
  · have e : 31129845205681 - 1 = [2 ^ 4, 3 ^ 3, 5 ^ 1, 13 ^ 1, 17 ^ 1, 281 ^ 1, 232073 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31129845205681 - 1) / 2 = 15564922602840 from by norm_num]
      have h2 : (19 : ZMod 31129845205681) ^ 15564922602840 = ((31129845205680 : ℕ) : ZMod 31129845205681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31129845205681 - 1) / 3 = 10376615068560 from by norm_num]
      have h2 : (19 : ZMod 31129845205681) ^ 10376615068560 = ((15763990543087 : ℕ) : ZMod 31129845205681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31129845205681 - 1) / 5 = 6225969041136 from by norm_num]
      have h2 : (19 : ZMod 31129845205681) ^ 6225969041136 = ((7862545861837 : ℕ) : ZMod 31129845205681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31129845205681 - 1) / 13 = 2394603477360 from by norm_num]
      have h2 : (19 : ZMod 31129845205681) ^ 2394603477360 = ((933506620967 : ℕ) : ZMod 31129845205681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31129845205681 - 1) / 17 = 1831167365040 from by norm_num]
      have h2 : (19 : ZMod 31129845205681) ^ 1831167365040 = ((3024926457528 : ℕ) : ZMod 31129845205681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31129845205681 - 1) / 281 = 110782367280 from by norm_num]
      have h2 : (19 : ZMod 31129845205681) ^ 110782367280 = ((2263574625413 : ℕ) : ZMod 31129845205681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31129845205681 - 1) / 232073 = 134138160 from by norm_num]
      have h2 : (19 : ZMod 31129845205681) ^ 134138160 = ((4094954845433 : ℕ) : ZMod 31129845205681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5322960113892133441 : Nat.Prime 5322960113892133441 := by
  refine lucas_primality 5322960113892133441 (23 : ZMod 5322960113892133441) ?_ (fun q hq hd => ?_)
  · rw [show 5322960113892133441 - 1 = 5322960113892133440 from by norm_num]
    reduce_mod_char
  · have e : 5322960113892133441 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 7 ^ 1, 13 ^ 4, 17 ^ 1, 809 ^ 1, 1217 ^ 1, 1657 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5322960113892133441 - 1) / 2 = 2661480056946066720 from by norm_num]
      have h2 : (23 : ZMod 5322960113892133441) ^ 2661480056946066720 = ((5322960113892133440 : ℕ) : ZMod 5322960113892133441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5322960113892133441 - 1) / 3 = 1774320037964044480 from by norm_num]
      have h2 : (23 : ZMod 5322960113892133441) ^ 1774320037964044480 = ((479007443090340667 : ℕ) : ZMod 5322960113892133441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5322960113892133441 - 1) / 5 = 1064592022778426688 from by norm_num]
      have h2 : (23 : ZMod 5322960113892133441) ^ 1064592022778426688 = ((2285472874329870146 : ℕ) : ZMod 5322960113892133441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5322960113892133441 - 1) / 7 = 760422873413161920 from by norm_num]
      have h2 : (23 : ZMod 5322960113892133441) ^ 760422873413161920 = ((4025366336020900521 : ℕ) : ZMod 5322960113892133441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5322960113892133441 - 1) / 13 = 409458470299394880 from by norm_num]
      have h2 : (23 : ZMod 5322960113892133441) ^ 409458470299394880 = ((2884468710315307356 : ℕ) : ZMod 5322960113892133441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5322960113892133441 - 1) / 17 = 313115300817184320 from by norm_num]
      have h2 : (23 : ZMod 5322960113892133441) ^ 313115300817184320 = ((2162952216395656885 : ℕ) : ZMod 5322960113892133441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5322960113892133441 - 1) / 809 = 6579678756356160 from by norm_num]
      have h2 : (23 : ZMod 5322960113892133441) ^ 6579678756356160 = ((4659125484309364466 : ℕ) : ZMod 5322960113892133441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5322960113892133441 - 1) / 1217 = 4373837398432320 from by norm_num]
      have h2 : (23 : ZMod 5322960113892133441) ^ 4373837398432320 = ((433703328470745690 : ℕ) : ZMod 5322960113892133441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5322960113892133441 - 1) / 1657 = 3212408034937920 from by norm_num]
      have h2 : (23 : ZMod 5322960113892133441) ^ 3212408034937920 = ((2733213927825350556 : ℕ) : ZMod 5322960113892133441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_187344375361201003441 : Nat.Prime 187344375361201003441 := by
  refine lucas_primality 187344375361201003441 (7 : ZMod 187344375361201003441) ?_ (fun q hq hd => ?_)
  · rw [show 187344375361201003441 - 1 = 187344375361201003440 from by norm_num]
    reduce_mod_char
  · have e : 187344375361201003441 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 11 ^ 1, 17 ^ 1, 31 ^ 1, 13913 ^ 1, 54217 ^ 1, 178513 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187344375361201003441 - 1) / 2 = 93672187680600501720 from by norm_num]
      have h2 : (7 : ZMod 187344375361201003441) ^ 93672187680600501720 = ((187344375361201003440 : ℕ) : ZMod 187344375361201003441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187344375361201003441 - 1) / 3 = 62448125120400334480 from by norm_num]
      have h2 : (7 : ZMod 187344375361201003441) ^ 62448125120400334480 = ((151074112745837592689 : ℕ) : ZMod 187344375361201003441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187344375361201003441 - 1) / 5 = 37468875072240200688 from by norm_num]
      have h2 : (7 : ZMod 187344375361201003441) ^ 37468875072240200688 = ((177997278617638054719 : ℕ) : ZMod 187344375361201003441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187344375361201003441 - 1) / 11 = 17031306851018273040 from by norm_num]
      have h2 : (7 : ZMod 187344375361201003441) ^ 17031306851018273040 = ((66886178376851379664 : ℕ) : ZMod 187344375361201003441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187344375361201003441 - 1) / 17 = 11020257374188294320 from by norm_num]
      have h2 : (7 : ZMod 187344375361201003441) ^ 11020257374188294320 = ((55498232022066697395 : ℕ) : ZMod 187344375361201003441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187344375361201003441 - 1) / 31 = 6043366947135516240 from by norm_num]
      have h2 : (7 : ZMod 187344375361201003441) ^ 6043366947135516240 = ((2712327342107032316 : ℕ) : ZMod 187344375361201003441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187344375361201003441 - 1) / 13913 = 13465419058520880 from by norm_num]
      have h2 : (7 : ZMod 187344375361201003441) ^ 13465419058520880 = ((95138739146420144888 : ℕ) : ZMod 187344375361201003441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187344375361201003441 - 1) / 54217 = 3455454476662320 from by norm_num]
      have h2 : (7 : ZMod 187344375361201003441) ^ 3455454476662320 = ((115422375990419231374 : ℕ) : ZMod 187344375361201003441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187344375361201003441 - 1) / 178513 = 1049471889224880 from by norm_num]
      have h2 : (7 : ZMod 187344375361201003441) ^ 1049471889224880 = ((58521660825565052709 : ℕ) : ZMod 187344375361201003441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_391522268549910113761 : Nat.Prime 391522268549910113761 := by
  refine lucas_primality 391522268549910113761 (7 : ZMod 391522268549910113761) ?_ (fun q hq hd => ?_)
  · rw [show 391522268549910113761 - 1 = 391522268549910113760 from by norm_num]
    reduce_mod_char
  · have e : 391522268549910113761 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 17 ^ 1, 41 ^ 1, 3769 ^ 1, 83641 ^ 1, 3712249 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (391522268549910113761 - 1) / 2 = 195761134274955056880 from by norm_num]
      have h2 : (7 : ZMod 391522268549910113761) ^ 195761134274955056880 = ((391522268549910113760 : ℕ) : ZMod 391522268549910113761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (391522268549910113761 - 1) / 3 = 130507422849970037920 from by norm_num]
      have h2 : (7 : ZMod 391522268549910113761) ^ 130507422849970037920 = ((231271064225077831481 : ℕ) : ZMod 391522268549910113761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (391522268549910113761 - 1) / 5 = 78304453709982022752 from by norm_num]
      have h2 : (7 : ZMod 391522268549910113761) ^ 78304453709982022752 = ((31905389043854728245 : ℕ) : ZMod 391522268549910113761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (391522268549910113761 - 1) / 17 = 23030721679406477280 from by norm_num]
      have h2 : (7 : ZMod 391522268549910113761) ^ 23030721679406477280 = ((326851294368334798426 : ℕ) : ZMod 391522268549910113761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (391522268549910113761 - 1) / 41 = 9549323623168539360 from by norm_num]
      have h2 : (7 : ZMod 391522268549910113761) ^ 9549323623168539360 = ((61310283255149987668 : ℕ) : ZMod 391522268549910113761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (391522268549910113761 - 1) / 3769 = 103879614897827040 from by norm_num]
      have h2 : (7 : ZMod 391522268549910113761) ^ 103879614897827040 = ((14508914975452326175 : ℕ) : ZMod 391522268549910113761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (391522268549910113761 - 1) / 83641 = 4680985025883360 from by norm_num]
      have h2 : (7 : ZMod 391522268549910113761) ^ 4680985025883360 = ((137293625435670238408 : ℕ) : ZMod 391522268549910113761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (391522268549910113761 - 1) / 3712249 = 105467674326240 from by norm_num]
      have h2 : (7 : ZMod 391522268549910113761) ^ 105467674326240 = ((20601890820612504744 : ℕ) : ZMod 391522268549910113761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_617835950261219632321 : Nat.Prime 617835950261219632321 := by
  refine lucas_primality 617835950261219632321 (13 : ZMod 617835950261219632321) ?_ (fun q hq hd => ?_)
  · rw [show 617835950261219632321 - 1 = 617835950261219632320 from by norm_num]
    reduce_mod_char
  · have e : 617835950261219632321 - 1 = [2 ^ 6, 3 ^ 3, 5 ^ 1, 7 ^ 1, 17 ^ 1, 31 ^ 1, 89 ^ 1, 18749 ^ 1, 11616697 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (617835950261219632321 - 1) / 2 = 308917975130609816160 from by norm_num]
      have h2 : (13 : ZMod 617835950261219632321) ^ 308917975130609816160 = ((617835950261219632320 : ℕ) : ZMod 617835950261219632321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (617835950261219632321 - 1) / 3 = 205945316753739877440 from by norm_num]
      have h2 : (13 : ZMod 617835950261219632321) ^ 205945316753739877440 = ((193295184803823204143 : ℕ) : ZMod 617835950261219632321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (617835950261219632321 - 1) / 5 = 123567190052243926464 from by norm_num]
      have h2 : (13 : ZMod 617835950261219632321) ^ 123567190052243926464 = ((135041647953987295650 : ℕ) : ZMod 617835950261219632321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (617835950261219632321 - 1) / 7 = 88262278608745661760 from by norm_num]
      have h2 : (13 : ZMod 617835950261219632321) ^ 88262278608745661760 = ((65551264838099969656 : ℕ) : ZMod 617835950261219632321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (617835950261219632321 - 1) / 17 = 36343291191836448960 from by norm_num]
      have h2 : (13 : ZMod 617835950261219632321) ^ 36343291191836448960 = ((502873660097882331170 : ℕ) : ZMod 617835950261219632321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (617835950261219632321 - 1) / 31 = 19930191943910310720 from by norm_num]
      have h2 : (13 : ZMod 617835950261219632321) ^ 19930191943910310720 = ((197976818676267501944 : ℕ) : ZMod 617835950261219632321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (617835950261219632321 - 1) / 89 = 6941976969227186880 from by norm_num]
      have h2 : (13 : ZMod 617835950261219632321) ^ 6941976969227186880 = ((203867665893113277926 : ℕ) : ZMod 617835950261219632321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (617835950261219632321 - 1) / 18749 = 32953008174367680 from by norm_num]
      have h2 : (13 : ZMod 617835950261219632321) ^ 32953008174367680 = ((444664815012419945237 : ℕ) : ZMod 617835950261219632321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (617835950261219632321 - 1) / 11616697 = 53185165306560 from by norm_num]
      have h2 : (13 : ZMod 617835950261219632321) ^ 53185165306560 = ((235395380913004348708 : ℕ) : ZMod 617835950261219632321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_308917975130609816161 : Nat.Prime 308917975130609816161 := by
  refine lucas_primality 308917975130609816161 (13 : ZMod 308917975130609816161) ?_ (fun q hq hd => ?_)
  · rw [show 308917975130609816161 - 1 = 308917975130609816160 from by norm_num]
    reduce_mod_char
  · have e : 308917975130609816161 - 1 = [2 ^ 5, 3 ^ 3, 5 ^ 1, 7 ^ 1, 17 ^ 1, 31 ^ 1, 89 ^ 1, 18749 ^ 1, 11616697 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308917975130609816161 - 1) / 2 = 154458987565304908080 from by norm_num]
      have h2 : (13 : ZMod 308917975130609816161) ^ 154458987565304908080 = ((308917975130609816160 : ℕ) : ZMod 308917975130609816161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308917975130609816161 - 1) / 3 = 102972658376869938720 from by norm_num]
      have h2 : (13 : ZMod 308917975130609816161) ^ 102972658376869938720 = ((17576062560 : ℕ) : ZMod 308917975130609816161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308917975130609816161 - 1) / 5 = 61783595026121963232 from by norm_num]
      have h2 : (13 : ZMod 308917975130609816161) ^ 61783595026121963232 = ((206590181932928584910 : ℕ) : ZMod 308917975130609816161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308917975130609816161 - 1) / 7 = 44131139304372830880 from by norm_num]
      have h2 : (13 : ZMod 308917975130609816161) ^ 44131139304372830880 = ((167825244286979190014 : ℕ) : ZMod 308917975130609816161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308917975130609816161 - 1) / 17 = 18171645595918224480 from by norm_num]
      have h2 : (13 : ZMod 308917975130609816161) ^ 18171645595918224480 = ((115321492361953978636 : ℕ) : ZMod 308917975130609816161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308917975130609816161 - 1) / 31 = 9965095971955155360 from by norm_num]
      have h2 : (13 : ZMod 308917975130609816161) ^ 9965095971955155360 = ((93065406286446501689 : ℕ) : ZMod 308917975130609816161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308917975130609816161 - 1) / 89 = 3470988484613593440 from by norm_num]
      have h2 : (13 : ZMod 308917975130609816161) ^ 3470988484613593440 = ((295851381508786004267 : ℕ) : ZMod 308917975130609816161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308917975130609816161 - 1) / 18749 = 16476504087183840 from by norm_num]
      have h2 : (13 : ZMod 308917975130609816161) ^ 16476504087183840 = ((121238973810406622614 : ℕ) : ZMod 308917975130609816161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308917975130609816161 - 1) / 11616697 = 26592582653280 from by norm_num]
      have h2 : (13 : ZMod 308917975130609816161) ^ 26592582653280 = ((292298248863797292695 : ℕ) : ZMod 308917975130609816161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_154458987565304908081 : Nat.Prime 154458987565304908081 := by
  refine lucas_primality 154458987565304908081 (22 : ZMod 154458987565304908081) ?_ (fun q hq hd => ?_)
  · rw [show 154458987565304908081 - 1 = 154458987565304908080 from by norm_num]
    reduce_mod_char
  · have e : 154458987565304908081 - 1 = [2 ^ 4, 3 ^ 3, 5 ^ 1, 7 ^ 1, 17 ^ 1, 31 ^ 1, 89 ^ 1, 18749 ^ 1, 11616697 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (154458987565304908081 - 1) / 2 = 77229493782652454040 from by norm_num]
      have h2 : (22 : ZMod 154458987565304908081) ^ 77229493782652454040 = ((154458987565304908080 : ℕ) : ZMod 154458987565304908081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (154458987565304908081 - 1) / 3 = 51486329188434969360 from by norm_num]
      have h2 : (22 : ZMod 154458987565304908081) ^ 51486329188434969360 = ((153707719926768190867 : ℕ) : ZMod 154458987565304908081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (154458987565304908081 - 1) / 5 = 30891797513060981616 from by norm_num]
      have h2 : (22 : ZMod 154458987565304908081) ^ 30891797513060981616 = ((97257578762099617919 : ℕ) : ZMod 154458987565304908081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (154458987565304908081 - 1) / 7 = 22065569652186415440 from by norm_num]
      have h2 : (22 : ZMod 154458987565304908081) ^ 22065569652186415440 = ((62342317593246970955 : ℕ) : ZMod 154458987565304908081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (154458987565304908081 - 1) / 17 = 9085822797959112240 from by norm_num]
      have h2 : (22 : ZMod 154458987565304908081) ^ 9085822797959112240 = ((121276897999462730936 : ℕ) : ZMod 154458987565304908081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (154458987565304908081 - 1) / 31 = 4982547985977577680 from by norm_num]
      have h2 : (22 : ZMod 154458987565304908081) ^ 4982547985977577680 = ((74477710659929038377 : ℕ) : ZMod 154458987565304908081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (154458987565304908081 - 1) / 89 = 1735494242306796720 from by norm_num]
      have h2 : (22 : ZMod 154458987565304908081) ^ 1735494242306796720 = ((28954775254526202272 : ℕ) : ZMod 154458987565304908081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (154458987565304908081 - 1) / 18749 = 8238252043591920 from by norm_num]
      have h2 : (22 : ZMod 154458987565304908081) ^ 8238252043591920 = ((128502659349271340404 : ℕ) : ZMod 154458987565304908081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (154458987565304908081 - 1) / 11616697 = 13296291326640 from by norm_num]
      have h2 : (22 : ZMod 154458987565304908081) ^ 13296291326640 = ((82062916363309179529 : ℕ) : ZMod 154458987565304908081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_230251457 : Nat.Prime 230251457 := by
  refine lucas_primality 230251457 (3 : ZMod 230251457) ?_ (fun q hq hd => ?_)
  · rw [show 230251457 - 1 = 230251456 from by norm_num]
    reduce_mod_char
  · have e : 230251457 - 1 = [2 ^ 6, 1789 ^ 1, 2011 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (230251457 - 1) / 2 = 115125728 from by norm_num]
      have h2 : (3 : ZMod 230251457) ^ 115125728 = ((230251456 : ℕ) : ZMod 230251457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (230251457 - 1) / 1789 = 128704 from by norm_num]
      have h2 : (3 : ZMod 230251457) ^ 128704 = ((108748013 : ℕ) : ZMod 230251457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (230251457 - 1) / 2011 = 114496 from by norm_num]
      have h2 : (3 : ZMod 230251457) ^ 114496 = ((101120855 : ℕ) : ZMod 230251457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1709413193 : Nat.Prime 1709413193 := by
  refine lucas_primality 1709413193 (3 : ZMod 1709413193) ?_ (fun q hq hd => ?_)
  · rw [show 1709413193 - 1 = 1709413192 from by norm_num]
    reduce_mod_char
  · have e : 1709413193 - 1 = [2 ^ 3, 313 ^ 1, 682673 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1709413193 - 1) / 2 = 854706596 from by norm_num]
      have h2 : (3 : ZMod 1709413193) ^ 854706596 = ((1709413192 : ℕ) : ZMod 1709413193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1709413193 - 1) / 313 = 5461384 from by norm_num]
      have h2 : (3 : ZMod 1709413193) ^ 5461384 = ((723984064 : ℕ) : ZMod 1709413193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1709413193 - 1) / 682673 = 2504 from by norm_num]
      have h2 : (3 : ZMod 1709413193) ^ 2504 = ((99644709 : ℕ) : ZMod 1709413193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1688970022366499085361 : Nat.Prime 1688970022366499085361 := by
  refine lucas_primality 1688970022366499085361 (19 : ZMod 1688970022366499085361) ?_ (fun q hq hd => ?_)
  · rw [show 1688970022366499085361 - 1 = 1688970022366499085360 from by norm_num]
    reduce_mod_char
  · have e : 1688970022366499085361 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 7 ^ 2, 17 ^ 1, 41 ^ 1, 149 ^ 1, 809 ^ 1, 1709413193 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1688970022366499085361 - 1) / 2 = 844485011183249542680 from by norm_num]
      have h2 : (19 : ZMod 1688970022366499085361) ^ 844485011183249542680 = ((1688970022366499085360 : ℕ) : ZMod 1688970022366499085361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1688970022366499085361 - 1) / 3 = 562990007455499695120 from by norm_num]
      have h2 : (19 : ZMod 1688970022366499085361) ^ 562990007455499695120 = ((313841957584733611173 : ℕ) : ZMod 1688970022366499085361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1688970022366499085361 - 1) / 5 = 337794004473299817072 from by norm_num]
      have h2 : (19 : ZMod 1688970022366499085361) ^ 337794004473299817072 = ((730393477472656836958 : ℕ) : ZMod 1688970022366499085361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1688970022366499085361 - 1) / 7 = 241281431766642726480 from by norm_num]
      have h2 : (19 : ZMod 1688970022366499085361) ^ 241281431766642726480 = ((1362093641708984841444 : ℕ) : ZMod 1688970022366499085361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1688970022366499085361 - 1) / 17 = 99351177786264652080 from by norm_num]
      have h2 : (19 : ZMod 1688970022366499085361) ^ 99351177786264652080 = ((1458175416256592498542 : ℕ) : ZMod 1688970022366499085361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1688970022366499085361 - 1) / 41 = 41194390789426806960 from by norm_num]
      have h2 : (19 : ZMod 1688970022366499085361) ^ 41194390789426806960 = ((687568052343683270415 : ℕ) : ZMod 1688970022366499085361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1688970022366499085361 - 1) / 149 = 11335369277627510640 from by norm_num]
      have h2 : (19 : ZMod 1688970022366499085361) ^ 11335369277627510640 = ((794475789489949900612 : ℕ) : ZMod 1688970022366499085361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1688970022366499085361 - 1) / 809 = 2087725614791717040 from by norm_num]
      have h2 : (19 : ZMod 1688970022366499085361) ^ 2087725614791717040 = ((556889674905279995470 : ℕ) : ZMod 1688970022366499085361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1709413193).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1688970022366499085361 - 1) / 1709413193 = 988040825520 from by norm_num]
      have h2 : (19 : ZMod 1688970022366499085361) ^ 988040825520 = ((1346243110665697671972 : ℕ) : ZMod 1688970022366499085361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_44695037407 : Nat.Prime 44695037407 := by
  refine lucas_primality 44695037407 (3 : ZMod 44695037407) ?_ (fun q hq hd => ?_)
  · rw [show 44695037407 - 1 = 44695037406 from by norm_num]
    reduce_mod_char
  · have e : 44695037407 - 1 = [2 ^ 1, 3 ^ 1, 103 ^ 1, 149 ^ 1, 485383 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44695037407 - 1) / 2 = 22347518703 from by norm_num]
      have h2 : (3 : ZMod 44695037407) ^ 22347518703 = ((44695037406 : ℕ) : ZMod 44695037407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44695037407 - 1) / 3 = 14898345802 from by norm_num]
      have h2 : (3 : ZMod 44695037407) ^ 14898345802 = ((15635013126 : ℕ) : ZMod 44695037407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44695037407 - 1) / 103 = 433932402 from by norm_num]
      have h2 : (3 : ZMod 44695037407) ^ 433932402 = ((43111269437 : ℕ) : ZMod 44695037407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44695037407 - 1) / 149 = 299966694 from by norm_num]
      have h2 : (3 : ZMod 44695037407) ^ 299966694 = ((35163323908 : ℕ) : ZMod 44695037407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44695037407 - 1) / 485383 = 92082 from by norm_num]
      have h2 : (3 : ZMod 44695037407) ^ 92082 = ((9108250834 : ℕ) : ZMod 44695037407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4632458802461936442001 : Nat.Prime 4632458802461936442001 := by
  refine lucas_primality 4632458802461936442001 (7 : ZMod 4632458802461936442001) ?_ (fun q hq hd => ?_)
  · rw [show 4632458802461936442001 - 1 = 4632458802461936442000 from by norm_num]
    reduce_mod_char
  · have e : 4632458802461936442001 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 3, 17 ^ 1, 31 ^ 1, 73 ^ 1, 139 ^ 1, 25657 ^ 1, 1875793 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4632458802461936442001 - 1) / 2 = 2316229401230968221000 from by norm_num]
      have h2 : (7 : ZMod 4632458802461936442001) ^ 2316229401230968221000 = ((4632458802461936442000 : ℕ) : ZMod 4632458802461936442001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4632458802461936442001 - 1) / 3 = 1544152934153978814000 from by norm_num]
      have h2 : (7 : ZMod 4632458802461936442001) ^ 1544152934153978814000 = ((2824095767483113999563 : ℕ) : ZMod 4632458802461936442001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4632458802461936442001 - 1) / 5 = 926491760492387288400 from by norm_num]
      have h2 : (7 : ZMod 4632458802461936442001) ^ 926491760492387288400 = ((2725552651604867361331 : ℕ) : ZMod 4632458802461936442001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4632458802461936442001 - 1) / 17 = 272497576615408026000 from by norm_num]
      have h2 : (7 : ZMod 4632458802461936442001) ^ 272497576615408026000 = ((4121666342549931232022 : ℕ) : ZMod 4632458802461936442001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4632458802461936442001 - 1) / 31 = 149434154918126982000 from by norm_num]
      have h2 : (7 : ZMod 4632458802461936442001) ^ 149434154918126982000 = ((2778421075716455381935 : ℕ) : ZMod 4632458802461936442001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4632458802461936442001 - 1) / 73 = 63458339759752554000 from by norm_num]
      have h2 : (7 : ZMod 4632458802461936442001) ^ 63458339759752554000 = ((454843032959924251672 : ℕ) : ZMod 4632458802461936442001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4632458802461936442001 - 1) / 139 = 33327041744330478000 from by norm_num]
      have h2 : (7 : ZMod 4632458802461936442001) ^ 33327041744330478000 = ((3784997188369603435744 : ℕ) : ZMod 4632458802461936442001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4632458802461936442001 - 1) / 25657 = 180553408522506000 from by norm_num]
      have h2 : (7 : ZMod 4632458802461936442001) ^ 180553408522506000 = ((2736527710743310489002 : ℕ) : ZMod 4632458802461936442001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4632458802461936442001 - 1) / 1875793 = 2469600218394000 from by norm_num]
      have h2 : (7 : ZMod 4632458802461936442001) ^ 2469600218394000 = ((4273839752542140666278 : ℕ) : ZMod 4632458802461936442001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_159805526897 : Nat.Prime 159805526897 := by
  refine lucas_primality 159805526897 (3 : ZMod 159805526897) ?_ (fun q hq hd => ?_)
  · rw [show 159805526897 - 1 = 159805526896 from by norm_num]
    reduce_mod_char
  · have e : 159805526897 - 1 = [2 ^ 4, 61 ^ 1, 197 ^ 2, 4219 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159805526897 - 1) / 2 = 79902763448 from by norm_num]
      have h2 : (3 : ZMod 159805526897) ^ 79902763448 = ((159805526896 : ℕ) : ZMod 159805526897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159805526897 - 1) / 61 = 2619762736 from by norm_num]
      have h2 : (3 : ZMod 159805526897) ^ 2619762736 = ((81113397311 : ℕ) : ZMod 159805526897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159805526897 - 1) / 197 = 811195568 from by norm_num]
      have h2 : (3 : ZMod 159805526897) ^ 811195568 = ((19347776015 : ℕ) : ZMod 159805526897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159805526897 - 1) / 4219 = 37877584 from by norm_num]
      have h2 : (3 : ZMod 159805526897) ^ 37877584 = ((86918510738 : ℕ) : ZMod 159805526897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6142943339981990979841 : Nat.Prime 6142943339981990979841 := by
  refine lucas_primality 6142943339981990979841 (7 : ZMod 6142943339981990979841) ?_ (fun q hq hd => ?_)
  · rw [show 6142943339981990979841 - 1 = 6142943339981990979840 from by norm_num]
    reduce_mod_char
  · have e : 6142943339981990979841 - 1 = [2 ^ 8, 3 ^ 2, 5 ^ 1, 13 ^ 2, 17 ^ 2, 41 ^ 1, 197 ^ 1, 1351728281 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6142943339981990979841 - 1) / 2 = 3071471669990995489920 from by norm_num]
      have h2 : (7 : ZMod 6142943339981990979841) ^ 3071471669990995489920 = ((6142943339981990979840 : ℕ) : ZMod 6142943339981990979841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6142943339981990979841 - 1) / 3 = 2047647779993996993280 from by norm_num]
      have h2 : (7 : ZMod 6142943339981990979841) ^ 2047647779993996993280 = ((2488760029108608127281 : ℕ) : ZMod 6142943339981990979841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6142943339981990979841 - 1) / 5 = 1228588667996398195968 from by norm_num]
      have h2 : (7 : ZMod 6142943339981990979841) ^ 1228588667996398195968 = ((4831843815929851032368 : ℕ) : ZMod 6142943339981990979841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6142943339981990979841 - 1) / 13 = 472534103075537767680 from by norm_num]
      have h2 : (7 : ZMod 6142943339981990979841) ^ 472534103075537767680 = ((1729395982672160015388 : ℕ) : ZMod 6142943339981990979841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6142943339981990979841 - 1) / 17 = 361349608234234763520 from by norm_num]
      have h2 : (7 : ZMod 6142943339981990979841) ^ 361349608234234763520 = ((190923987703541082134 : ℕ) : ZMod 6142943339981990979841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6142943339981990979841 - 1) / 41 = 149827886341024170240 from by norm_num]
      have h2 : (7 : ZMod 6142943339981990979841) ^ 149827886341024170240 = ((6063386863067679483866 : ℕ) : ZMod 6142943339981990979841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6142943339981990979841 - 1) / 197 = 31182453502446654720 from by norm_num]
      have h2 : (7 : ZMod 6142943339981990979841) ^ 31182453502446654720 = ((3660252589286864604910 : ℕ) : ZMod 6142943339981990979841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1351728281).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6142943339981990979841 - 1) / 1351728281 = 4544510480640 from by norm_num]
      have h2 : (7 : ZMod 6142943339981990979841) ^ 4544510480640 = ((2590801450044973918234 : ℕ) : ZMod 6142943339981990979841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_304237489 : Nat.Prime 304237489 := by
  refine lucas_primality 304237489 (7 : ZMod 304237489) ?_ (fun q hq hd => ?_)
  · rw [show 304237489 - 1 = 304237488 from by norm_num]
    reduce_mod_char
  · have e : 304237489 - 1 = [2 ^ 4, 3 ^ 1, 6338281 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (304237489 - 1) / 2 = 152118744 from by norm_num]
      have h2 : (7 : ZMod 304237489) ^ 152118744 = ((304237488 : ℕ) : ZMod 304237489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (304237489 - 1) / 3 = 101412496 from by norm_num]
      have h2 : (7 : ZMod 304237489) ^ 101412496 = ((243640312 : ℕ) : ZMod 304237489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (304237489 - 1) / 6338281 = 48 from by norm_num]
      have h2 : (7 : ZMod 304237489) ^ 48 = ((22462450 : ℕ) : ZMod 304237489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3839872682369 : Nat.Prime 3839872682369 := by
  refine lucas_primality 3839872682369 (3 : ZMod 3839872682369) ?_ (fun q hq hd => ?_)
  · rw [show 3839872682369 - 1 = 3839872682368 from by norm_num]
    reduce_mod_char
  · have e : 3839872682369 - 1 = [2 ^ 7, 1249 ^ 1, 24018419 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3839872682369 - 1) / 2 = 1919936341184 from by norm_num]
      have h2 : (3 : ZMod 3839872682369) ^ 1919936341184 = ((3839872682368 : ℕ) : ZMod 3839872682369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3839872682369 - 1) / 1249 = 3074357632 from by norm_num]
      have h2 : (3 : ZMod 3839872682369) ^ 3074357632 = ((2377498526167 : ℕ) : ZMod 3839872682369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3839872682369 - 1) / 24018419 = 159872 from by norm_num]
      have h2 : (3 : ZMod 3839872682369) ^ 159872 = ((2059626728605 : ℕ) : ZMod 3839872682369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_258426017 : Nat.Prime 258426017 := by
  refine lucas_primality 258426017 (3 : ZMod 258426017) ?_ (fun q hq hd => ?_)
  · rw [show 258426017 - 1 = 258426016 from by norm_num]
    reduce_mod_char
  · have e : 258426017 - 1 = [2 ^ 5, 173 ^ 1, 46681 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (258426017 - 1) / 2 = 129213008 from by norm_num]
      have h2 : (3 : ZMod 258426017) ^ 129213008 = ((258426016 : ℕ) : ZMod 258426017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (258426017 - 1) / 173 = 1493792 from by norm_num]
      have h2 : (3 : ZMod 258426017) ^ 1493792 = ((68396593 : ℕ) : ZMod 258426017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (258426017 - 1) / 46681 = 5536 from by norm_num]
      have h2 : (3 : ZMod 258426017) ^ 5536 = ((57699234 : ℕ) : ZMod 258426017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_16013775593 : Nat.Prime 16013775593 := by
  refine lucas_primality 16013775593 (3 : ZMod 16013775593) ?_ (fun q hq hd => ?_)
  · rw [show 16013775593 - 1 = 16013775592 from by norm_num]
    reduce_mod_char
  · have e : 16013775593 - 1 = [2 ^ 3, 67 ^ 1, 2837 ^ 1, 10531 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16013775593 - 1) / 2 = 8006887796 from by norm_num]
      have h2 : (3 : ZMod 16013775593) ^ 8006887796 = ((16013775592 : ℕ) : ZMod 16013775593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16013775593 - 1) / 67 = 239011576 from by norm_num]
      have h2 : (3 : ZMod 16013775593) ^ 239011576 = ((402845746 : ℕ) : ZMod 16013775593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16013775593 - 1) / 2837 = 5644616 from by norm_num]
      have h2 : (3 : ZMod 16013775593) ^ 5644616 = ((4270240951 : ℕ) : ZMod 16013775593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16013775593 - 1) / 10531 = 1520632 from by norm_num]
      have h2 : (3 : ZMod 16013775593) ^ 1520632 = ((9359039550 : ℕ) : ZMod 16013775593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_148222903052887857582961 : Nat.Prime 148222903052887857582961 := by
  refine lucas_primality 148222903052887857582961 (19 : ZMod 148222903052887857582961) ?_ (fun q hq hd => ?_)
  · rw [show 148222903052887857582961 - 1 = 148222903052887857582960 from by norm_num]
    reduce_mod_char
  · have e : 148222903052887857582961 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 11 ^ 1, 13 ^ 1, 17 ^ 1, 43 ^ 1, 137 ^ 1, 2693 ^ 1, 16013775593 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (148222903052887857582961 - 1) / 2 = 74111451526443928791480 from by norm_num]
      have h2 : (19 : ZMod 148222903052887857582961) ^ 74111451526443928791480 = ((148222903052887857582960 : ℕ) : ZMod 148222903052887857582961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (148222903052887857582961 - 1) / 3 = 49407634350962619194320 from by norm_num]
      have h2 : (19 : ZMod 148222903052887857582961) ^ 49407634350962619194320 = ((74711190071700642766264 : ℕ) : ZMod 148222903052887857582961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (148222903052887857582961 - 1) / 5 = 29644580610577571516592 from by norm_num]
      have h2 : (19 : ZMod 148222903052887857582961) ^ 29644580610577571516592 = ((97655409073520151933651 : ℕ) : ZMod 148222903052887857582961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (148222903052887857582961 - 1) / 11 = 13474809368444350689360 from by norm_num]
      have h2 : (19 : ZMod 148222903052887857582961) ^ 13474809368444350689360 = ((100945967511233799781657 : ℕ) : ZMod 148222903052887857582961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (148222903052887857582961 - 1) / 13 = 11401761773299065967920 from by norm_num]
      have h2 : (19 : ZMod 148222903052887857582961) ^ 11401761773299065967920 = ((90479880960977931974858 : ℕ) : ZMod 148222903052887857582961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (148222903052887857582961 - 1) / 17 = 8718994297228697504880 from by norm_num]
      have h2 : (19 : ZMod 148222903052887857582961) ^ 8718994297228697504880 = ((77781450901128819620997 : ℕ) : ZMod 148222903052887857582961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (148222903052887857582961 - 1) / 43 = 3447044257043903664720 from by norm_num]
      have h2 : (19 : ZMod 148222903052887857582961) ^ 3447044257043903664720 = ((27375643209903193002734 : ℕ) : ZMod 148222903052887857582961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (148222903052887857582961 - 1) / 137 = 1081919000386042756080 from by norm_num]
      have h2 : (19 : ZMod 148222903052887857582961) ^ 1081919000386042756080 = ((103122243715862512358000 : ℕ) : ZMod 148222903052887857582961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (148222903052887857582961 - 1) / 2693 = 55040067973593708720 from by norm_num]
      have h2 : (19 : ZMod 148222903052887857582961) ^ 55040067973593708720 = ((113419930287194512502293 : ℕ) : ZMod 148222903052887857582961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_16013775593).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (148222903052887857582961 - 1) / 16013775593 = 9255962292720 from by norm_num]
      have h2 : (19 : ZMod 148222903052887857582961) ^ 9255962292720 = ((4396671571817664632815 : ℕ) : ZMod 148222903052887857582961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5844802782997 : Nat.Prime 5844802782997 := by
  refine lucas_primality 5844802782997 (5 : ZMod 5844802782997) ?_ (fun q hq hd => ?_)
  · rw [show 5844802782997 - 1 = 5844802782996 from by norm_num]
    reduce_mod_char
  · have e : 5844802782997 - 1 = [2 ^ 2, 3 ^ 3, 2099 ^ 1, 25783013 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5844802782997 - 1) / 2 = 2922401391498 from by norm_num]
      have h2 : (5 : ZMod 5844802782997) ^ 2922401391498 = ((5844802782996 : ℕ) : ZMod 5844802782997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5844802782997 - 1) / 3 = 1948267594332 from by norm_num]
      have h2 : (5 : ZMod 5844802782997) ^ 1948267594332 = ((5572568597916 : ℕ) : ZMod 5844802782997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5844802782997 - 1) / 2099 = 2784565404 from by norm_num]
      have h2 : (5 : ZMod 5844802782997) ^ 2784565404 = ((2764930648455 : ℕ) : ZMod 5844802782997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5844802782997 - 1) / 25783013 = 226692 from by norm_num]
      have h2 : (5 : ZMod 5844802782997) ^ 226692 = ((2283865981869 : ℕ) : ZMod 5844802782997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_169318049 : Nat.Prime 169318049 := by
  refine lucas_primality 169318049 (3 : ZMod 169318049) ?_ (fun q hq hd => ?_)
  · rw [show 169318049 - 1 = 169318048 from by norm_num]
    reduce_mod_char
  · have e : 169318049 - 1 = [2 ^ 5, 349 ^ 1, 15161 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169318049 - 1) / 2 = 84659024 from by norm_num]
      have h2 : (3 : ZMod 169318049) ^ 84659024 = ((169318048 : ℕ) : ZMod 169318049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169318049 - 1) / 349 = 485152 from by norm_num]
      have h2 : (3 : ZMod 169318049) ^ 485152 = ((64783065 : ℕ) : ZMod 169318049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169318049 - 1) / 15161 = 11168 from by norm_num]
      have h2 : (3 : ZMod 169318049) ^ 11168 = ((25133279 : ℕ) : ZMod 169318049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_590440230397776959593681 : Nat.Prime 590440230397776959593681 := by
  refine lucas_primality 590440230397776959593681 (11 : ZMod 590440230397776959593681) ?_ (fun q hq hd => ?_)
  · rw [show 590440230397776959593681 - 1 = 590440230397776959593680 from by norm_num]
    reduce_mod_char
  · have e : 590440230397776959593681 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 73 ^ 1, 233 ^ 1, 2237 ^ 1, 3209 ^ 1, 169318049 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (590440230397776959593681 - 1) / 2 = 295220115198888479796840 from by norm_num]
      have h2 : (11 : ZMod 590440230397776959593681) ^ 295220115198888479796840 = ((590440230397776959593680 : ℕ) : ZMod 590440230397776959593681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (590440230397776959593681 - 1) / 3 = 196813410132592319864560 from by norm_num]
      have h2 : (11 : ZMod 590440230397776959593681) ^ 196813410132592319864560 = ((254921573758117326786864 : ℕ) : ZMod 590440230397776959593681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (590440230397776959593681 - 1) / 5 = 118088046079555391918736 from by norm_num]
      have h2 : (11 : ZMod 590440230397776959593681) ^ 118088046079555391918736 = ((525316157413433658545761 : ℕ) : ZMod 590440230397776959593681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (590440230397776959593681 - 1) / 7 = 84348604342539565656240 from by norm_num]
      have h2 : (11 : ZMod 590440230397776959593681) ^ 84348604342539565656240 = ((68414341132712688404931 : ℕ) : ZMod 590440230397776959593681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (590440230397776959593681 - 1) / 17 = 34731778258692762329040 from by norm_num]
      have h2 : (11 : ZMod 590440230397776959593681) ^ 34731778258692762329040 = ((118554777801772502164626 : ℕ) : ZMod 590440230397776959593681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (590440230397776959593681 - 1) / 73 = 8088222334216122734160 from by norm_num]
      have h2 : (11 : ZMod 590440230397776959593681) ^ 8088222334216122734160 = ((377898461031761073196631 : ℕ) : ZMod 590440230397776959593681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (590440230397776959593681 - 1) / 233 = 2534078242050544890960 from by norm_num]
      have h2 : (11 : ZMod 590440230397776959593681) ^ 2534078242050544890960 = ((414970441997603996302227 : ℕ) : ZMod 590440230397776959593681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (590440230397776959593681 - 1) / 2237 = 263942883503700026640 from by norm_num]
      have h2 : (11 : ZMod 590440230397776959593681) ^ 263942883503700026640 = ((327158231897694958325730 : ℕ) : ZMod 590440230397776959593681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (590440230397776959593681 - 1) / 3209 = 183995085820435325520 from by norm_num]
      have h2 : (11 : ZMod 590440230397776959593681) ^ 183995085820435325520 = ((157947907406528233010910 : ℕ) : ZMod 590440230397776959593681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_169318049).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (590440230397776959593681 - 1) / 169318049 = 3487166512282320 from by norm_num]
      have h2 : (11 : ZMod 590440230397776959593681) ^ 3487166512282320 = ((170110332423670041574173 : ℕ) : ZMod 590440230397776959593681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_131435695777 : Nat.Prime 131435695777 := by
  refine lucas_primality 131435695777 (17 : ZMod 131435695777) ?_ (fun q hq hd => ?_)
  · rw [show 131435695777 - 1 = 131435695776 from by norm_num]
    reduce_mod_char
  · have e : 131435695777 - 1 = [2 ^ 5, 3 ^ 1, 7 ^ 1, 11 ^ 1, 311 ^ 1, 57173 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131435695777 - 1) / 2 = 65717847888 from by norm_num]
      have h2 : (17 : ZMod 131435695777) ^ 65717847888 = ((131435695776 : ℕ) : ZMod 131435695777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131435695777 - 1) / 3 = 43811898592 from by norm_num]
      have h2 : (17 : ZMod 131435695777) ^ 43811898592 = ((100042379793 : ℕ) : ZMod 131435695777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131435695777 - 1) / 7 = 18776527968 from by norm_num]
      have h2 : (17 : ZMod 131435695777) ^ 18776527968 = ((70634951081 : ℕ) : ZMod 131435695777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131435695777 - 1) / 11 = 11948699616 from by norm_num]
      have h2 : (17 : ZMod 131435695777) ^ 11948699616 = ((33797377118 : ℕ) : ZMod 131435695777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131435695777 - 1) / 311 = 422622816 from by norm_num]
      have h2 : (17 : ZMod 131435695777) ^ 422622816 = ((26917664432 : ℕ) : ZMod 131435695777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131435695777 - 1) / 57173 = 2298912 from by norm_num]
      have h2 : (17 : ZMod 131435695777) ^ 2298912 = ((63152034369 : ℕ) : ZMod 131435695777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_753732192488350417 : Nat.Prime 753732192488350417 := by
  refine lucas_primality 753732192488350417 (7 : ZMod 753732192488350417) ?_ (fun q hq hd => ?_)
  · rw [show 753732192488350417 - 1 = 753732192488350416 from by norm_num]
    reduce_mod_char
  · have e : 753732192488350417 - 1 = [2 ^ 4, 3 ^ 1, 11 ^ 1, 10861 ^ 1, 131435695777 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (753732192488350417 - 1) / 2 = 376866096244175208 from by norm_num]
      have h2 : (7 : ZMod 753732192488350417) ^ 376866096244175208 = ((753732192488350416 : ℕ) : ZMod 753732192488350417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (753732192488350417 - 1) / 3 = 251244064162783472 from by norm_num]
      have h2 : (7 : ZMod 753732192488350417) ^ 251244064162783472 = ((590882237538347826 : ℕ) : ZMod 753732192488350417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (753732192488350417 - 1) / 11 = 68521108408031856 from by norm_num]
      have h2 : (7 : ZMod 753732192488350417) ^ 68521108408031856 = ((25710321892790411 : ℕ) : ZMod 753732192488350417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (753732192488350417 - 1) / 10861 = 69398047370256 from by norm_num]
      have h2 : (7 : ZMod 753732192488350417) ^ 69398047370256 = ((176749811479342740 : ℕ) : ZMod 753732192488350417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_131435695777).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (753732192488350417 - 1) / 131435695777 = 5734608 from by norm_num]
      have h2 : (7 : ZMod 753732192488350417) ^ 5734608 = ((210115100605651384 : ℕ) : ZMod 753732192488350417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1095403448591351982886081 : Nat.Prime 1095403448591351982886081 := by
  refine lucas_primality 1095403448591351982886081 (7 : ZMod 1095403448591351982886081) ?_ (fun q hq hd => ?_)
  · rw [show 1095403448591351982886081 - 1 = 1095403448591351982886080 from by norm_num]
    reduce_mod_char
  · have e : 1095403448591351982886081 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 17 ^ 1, 19 ^ 1, 23 ^ 1, 29 ^ 1, 102673 ^ 1, 121661 ^ 1, 424001 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095403448591351982886081 - 1) / 2 = 547701724295675991443040 from by norm_num]
      have h2 : (7 : ZMod 1095403448591351982886081) ^ 547701724295675991443040 = ((1095403448591351982886080 : ℕ) : ZMod 1095403448591351982886081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095403448591351982886081 - 1) / 3 = 365134482863783994295360 from by norm_num]
      have h2 : (7 : ZMod 1095403448591351982886081) ^ 365134482863783994295360 = ((289460296567326544967486 : ℕ) : ZMod 1095403448591351982886081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095403448591351982886081 - 1) / 5 = 219080689718270396577216 from by norm_num]
      have h2 : (7 : ZMod 1095403448591351982886081) ^ 219080689718270396577216 = ((497250603331662467769147 : ℕ) : ZMod 1095403448591351982886081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095403448591351982886081 - 1) / 17 = 64435496975961881346240 from by norm_num]
      have h2 : (7 : ZMod 1095403448591351982886081) ^ 64435496975961881346240 = ((378743063561177913725175 : ℕ) : ZMod 1095403448591351982886081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095403448591351982886081 - 1) / 19 = 57652813083755367520320 from by norm_num]
      have h2 : (7 : ZMod 1095403448591351982886081) ^ 57652813083755367520320 = ((886568615380837920813144 : ℕ) : ZMod 1095403448591351982886081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095403448591351982886081 - 1) / 23 = 47626236895276173168960 from by norm_num]
      have h2 : (7 : ZMod 1095403448591351982886081) ^ 47626236895276173168960 = ((893785107038003379037121 : ℕ) : ZMod 1095403448591351982886081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095403448591351982886081 - 1) / 29 = 37772532710046620099520 from by norm_num]
      have h2 : (7 : ZMod 1095403448591351982886081) ^ 37772532710046620099520 = ((139631844511227487434394 : ℕ) : ZMod 1095403448591351982886081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095403448591351982886081 - 1) / 102673 = 10668855965943840960 from by norm_num]
      have h2 : (7 : ZMod 1095403448591351982886081) ^ 10668855965943840960 = ((363410806030260643408378 : ℕ) : ZMod 1095403448591351982886081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095403448591351982886081 - 1) / 121661 = 9003735367877561280 from by norm_num]
      have h2 : (7 : ZMod 1095403448591351982886081) ^ 9003735367877561280 = ((52625529787566332974610 : ℕ) : ZMod 1095403448591351982886081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095403448591351982886081 - 1) / 424001 = 2583492606364966080 from by norm_num]
      have h2 : (7 : ZMod 1095403448591351982886081) ^ 2583492606364966080 = ((420091106579880746134947 : ℕ) : ZMod 1095403448591351982886081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_18295290017 : Nat.Prime 18295290017 := by
  refine lucas_primality 18295290017 (3 : ZMod 18295290017) ?_ (fun q hq hd => ?_)
  · rw [show 18295290017 - 1 = 18295290016 from by norm_num]
    reduce_mod_char
  · have e : 18295290017 - 1 = [2 ^ 5, 23 ^ 1, 3571 ^ 1, 6961 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18295290017 - 1) / 2 = 9147645008 from by norm_num]
      have h2 : (3 : ZMod 18295290017) ^ 9147645008 = ((18295290016 : ℕ) : ZMod 18295290017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18295290017 - 1) / 23 = 795447392 from by norm_num]
      have h2 : (3 : ZMod 18295290017) ^ 795447392 = ((13317023670 : ℕ) : ZMod 18295290017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18295290017 - 1) / 3571 = 5123296 from by norm_num]
      have h2 : (3 : ZMod 18295290017) ^ 5123296 = ((12555714256 : ℕ) : ZMod 18295290017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18295290017 - 1) / 6961 = 2628256 from by norm_num]
      have h2 : (3 : ZMod 18295290017) ^ 2628256 = ((8817363546 : ℕ) : ZMod 18295290017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_297457729 : Nat.Prime 297457729 := by
  refine lucas_primality 297457729 (23 : ZMod 297457729) ?_ (fun q hq hd => ?_)
  · rw [show 297457729 - 1 = 297457728 from by norm_num]
    reduce_mod_char
  · have e : 297457729 - 1 = [2 ^ 6, 3 ^ 1, 167 ^ 1, 9277 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297457729 - 1) / 2 = 148728864 from by norm_num]
      have h2 : (23 : ZMod 297457729) ^ 148728864 = ((297457728 : ℕ) : ZMod 297457729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297457729 - 1) / 3 = 99152576 from by norm_num]
      have h2 : (23 : ZMod 297457729) ^ 99152576 = ((101685871 : ℕ) : ZMod 297457729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297457729 - 1) / 167 = 1781184 from by norm_num]
      have h2 : (23 : ZMod 297457729) ^ 1781184 = ((2905440 : ℕ) : ZMod 297457729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297457729 - 1) / 9277 = 32064 from by norm_num]
      have h2 : (23 : ZMod 297457729) ^ 32064 = ((130456233 : ℕ) : ZMod 297457729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_19854587986529 : Nat.Prime 19854587986529 := by
  refine lucas_primality 19854587986529 (3 : ZMod 19854587986529) ?_ (fun q hq hd => ?_)
  · rw [show 19854587986529 - 1 = 19854587986528 from by norm_num]
    reduce_mod_char
  · have e : 19854587986529 - 1 = [2 ^ 5, 17 ^ 1, 23 ^ 2, 3779 ^ 1, 18257 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19854587986529 - 1) / 2 = 9927293993264 from by norm_num]
      have h2 : (3 : ZMod 19854587986529) ^ 9927293993264 = ((19854587986528 : ℕ) : ZMod 19854587986529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19854587986529 - 1) / 17 = 1167916940384 from by norm_num]
      have h2 : (3 : ZMod 19854587986529) ^ 1167916940384 = ((2493115507044 : ℕ) : ZMod 19854587986529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19854587986529 - 1) / 23 = 863242955936 from by norm_num]
      have h2 : (3 : ZMod 19854587986529) ^ 863242955936 = ((17589639963599 : ℕ) : ZMod 19854587986529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19854587986529 - 1) / 3779 = 5253926432 from by norm_num]
      have h2 : (3 : ZMod 19854587986529) ^ 5253926432 = ((15248847658771 : ℕ) : ZMod 19854587986529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19854587986529 - 1) / 18257 = 1087505504 from by norm_num]
      have h2 : (3 : ZMod 19854587986529) ^ 1087505504 = ((17900440818996 : ℕ) : ZMod 19854587986529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_85826901353 : Nat.Prime 85826901353 := by
  refine lucas_primality 85826901353 (3 : ZMod 85826901353) ?_ (fun q hq hd => ?_)
  · rw [show 85826901353 - 1 = 85826901352 from by norm_num]
    reduce_mod_char
  · have e : 85826901353 - 1 = [2 ^ 3, 17 ^ 1, 97 ^ 1, 701 ^ 1, 9281 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85826901353 - 1) / 2 = 42913450676 from by norm_num]
      have h2 : (3 : ZMod 85826901353) ^ 42913450676 = ((85826901352 : ℕ) : ZMod 85826901353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85826901353 - 1) / 17 = 5048641256 from by norm_num]
      have h2 : (3 : ZMod 85826901353) ^ 5048641256 = ((57638121014 : ℕ) : ZMod 85826901353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85826901353 - 1) / 97 = 884813416 from by norm_num]
      have h2 : (3 : ZMod 85826901353) ^ 884813416 = ((77843863355 : ℕ) : ZMod 85826901353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85826901353 - 1) / 701 = 122434952 from by norm_num]
      have h2 : (3 : ZMod 85826901353) ^ 122434952 = ((58244412718 : ℕ) : ZMod 85826901353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85826901353 - 1) / 9281 = 9247592 from by norm_num]
      have h2 : (3 : ZMod 85826901353) ^ 9247592 = ((3375662451 : ℕ) : ZMod 85826901353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4257696543602770772646001 : Nat.Prime 4257696543602770772646001 := by
  refine lucas_primality 4257696543602770772646001 (23 : ZMod 4257696543602770772646001) ?_ (fun q hq hd => ?_)
  · rw [show 4257696543602770772646001 - 1 = 4257696543602770772646000 from by norm_num]
    reduce_mod_char
  · have e : 4257696543602770772646001 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 3, 17 ^ 1, 109 ^ 1, 653 ^ 1, 6833 ^ 1, 85826901353 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4257696543602770772646001 - 1) / 2 = 2128848271801385386323000 from by norm_num]
      have h2 : (23 : ZMod 4257696543602770772646001) ^ 2128848271801385386323000 = ((4257696543602770772646000 : ℕ) : ZMod 4257696543602770772646001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4257696543602770772646001 - 1) / 3 = 1419232181200923590882000 from by norm_num]
      have h2 : (23 : ZMod 4257696543602770772646001) ^ 1419232181200923590882000 = ((1262503865815169254566361 : ℕ) : ZMod 4257696543602770772646001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4257696543602770772646001 - 1) / 5 = 851539308720554154529200 from by norm_num]
      have h2 : (23 : ZMod 4257696543602770772646001) ^ 851539308720554154529200 = ((2944447831058537353997286 : ℕ) : ZMod 4257696543602770772646001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4257696543602770772646001 - 1) / 17 = 250452737858986516038000 from by norm_num]
      have h2 : (23 : ZMod 4257696543602770772646001) ^ 250452737858986516038000 = ((2248915518086247382708826 : ℕ) : ZMod 4257696543602770772646001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4257696543602770772646001 - 1) / 109 = 39061436179841933694000 from by norm_num]
      have h2 : (23 : ZMod 4257696543602770772646001) ^ 39061436179841933694000 = ((3112685988464087989683004 : ℕ) : ZMod 4257696543602770772646001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4257696543602770772646001 - 1) / 653 = 6520209101995054782000 from by norm_num]
      have h2 : (23 : ZMod 4257696543602770772646001) ^ 6520209101995054782000 = ((2199475077556148845568600 : ℕ) : ZMod 4257696543602770772646001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4257696543602770772646001 - 1) / 6833 = 623107938475453062000 from by norm_num]
      have h2 : (23 : ZMod 4257696543602770772646001) ^ 623107938475453062000 = ((3278725428516616863093927 : ℕ) : ZMod 4257696543602770772646001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_85826901353).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4257696543602770772646001 - 1) / 85826901353 = 49607948982000 from by norm_num]
      have h2 : (23 : ZMod 4257696543602770772646001) ^ 49607948982000 = ((40148578956622738743043 : ℕ) : ZMod 4257696543602770772646001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_611380753 : Nat.Prime 611380753 := by
  refine lucas_primality 611380753 (5 : ZMod 611380753) ?_ (fun q hq hd => ?_)
  · rw [show 611380753 - 1 = 611380752 from by norm_num]
    reduce_mod_char
  · have e : 611380753 - 1 = [2 ^ 4, 3 ^ 1, 12737099 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (611380753 - 1) / 2 = 305690376 from by norm_num]
      have h2 : (5 : ZMod 611380753) ^ 305690376 = ((611380752 : ℕ) : ZMod 611380753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (611380753 - 1) / 3 = 203793584 from by norm_num]
      have h2 : (5 : ZMod 611380753) ^ 203793584 = ((82937474 : ℕ) : ZMod 611380753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (611380753 - 1) / 12737099 = 48 from by norm_num]
      have h2 : (5 : ZMod 611380753) ^ 48 = ((266728211 : ℕ) : ZMod 611380753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_305690377 : Nat.Prime 305690377 := by
  refine lucas_primality 305690377 (5 : ZMod 305690377) ?_ (fun q hq hd => ?_)
  · rw [show 305690377 - 1 = 305690376 from by norm_num]
    reduce_mod_char
  · have e : 305690377 - 1 = [2 ^ 3, 3 ^ 1, 12737099 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (305690377 - 1) / 2 = 152845188 from by norm_num]
      have h2 : (5 : ZMod 305690377) ^ 152845188 = ((305690376 : ℕ) : ZMod 305690377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (305690377 - 1) / 3 = 101896792 from by norm_num]
      have h2 : (5 : ZMod 305690377) ^ 101896792 = ((138691871 : ℕ) : ZMod 305690377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (305690377 - 1) / 12737099 = 24 from by norm_num]
      have h2 : (5 : ZMod 305690377) ^ 24 = ((39560824 : ℕ) : ZMod 305690377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1638724289 : Nat.Prime 1638724289 := by
  refine lucas_primality 1638724289 (3 : ZMod 1638724289) ?_ (fun q hq hd => ?_)
  · rw [show 1638724289 - 1 = 1638724288 from by norm_num]
    reduce_mod_char
  · have e : 1638724289 - 1 = [2 ^ 6, 25605067 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1638724289 - 1) / 2 = 819362144 from by norm_num]
      have h2 : (3 : ZMod 1638724289) ^ 819362144 = ((1638724288 : ℕ) : ZMod 1638724289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1638724289 - 1) / 25605067 = 64 from by norm_num]
      have h2 : (3 : ZMod 1638724289) ^ 64 = ((1210056614 : ℕ) : ZMod 1638724289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_260652952177 : Nat.Prime 260652952177 := by
  refine lucas_primality 260652952177 (5 : ZMod 260652952177) ?_ (fun q hq hd => ?_)
  · rw [show 260652952177 - 1 = 260652952176 from by norm_num]
    reduce_mod_char
  · have e : 260652952177 - 1 = [2 ^ 4, 3 ^ 1, 61 ^ 1, 179 ^ 1, 497323 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260652952177 - 1) / 2 = 130326476088 from by norm_num]
      have h2 : (5 : ZMod 260652952177) ^ 130326476088 = ((260652952176 : ℕ) : ZMod 260652952177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260652952177 - 1) / 3 = 86884317392 from by norm_num]
      have h2 : (5 : ZMod 260652952177) ^ 86884317392 = ((78728893963 : ℕ) : ZMod 260652952177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260652952177 - 1) / 61 = 4272999216 from by norm_num]
      have h2 : (5 : ZMod 260652952177) ^ 4272999216 = ((116084137988 : ℕ) : ZMod 260652952177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260652952177 - 1) / 179 = 1456161744 from by norm_num]
      have h2 : (5 : ZMod 260652952177) ^ 1456161744 = ((167548057890 : ℕ) : ZMod 260652952177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260652952177 - 1) / 497323 = 524112 from by norm_num]
      have h2 : (5 : ZMod 260652952177) ^ 524112 = ((239885768747 : ℕ) : ZMod 260652952177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_492217207 : Nat.Prime 492217207 := by
  refine lucas_primality 492217207 (3 : ZMod 492217207) ?_ (fun q hq hd => ?_)
  · rw [show 492217207 - 1 = 492217206 from by norm_num]
    reduce_mod_char
  · have e : 492217207 - 1 = [2 ^ 1, 3 ^ 1, 13 ^ 1, 6310477 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (492217207 - 1) / 2 = 246108603 from by norm_num]
      have h2 : (3 : ZMod 492217207) ^ 246108603 = ((492217206 : ℕ) : ZMod 492217207) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (492217207 - 1) / 3 = 164072402 from by norm_num]
      have h2 : (3 : ZMod 492217207) ^ 164072402 = ((199293474 : ℕ) : ZMod 492217207) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (492217207 - 1) / 13 = 37862862 from by norm_num]
      have h2 : (3 : ZMod 492217207) ^ 37862862 = ((460397912 : ℕ) : ZMod 492217207) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (492217207 - 1) / 6310477 = 78 from by norm_num]
      have h2 : (3 : ZMod 492217207) ^ 78 = ((52030274 : ℕ) : ZMod 492217207) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7875475313 : Nat.Prime 7875475313 := by
  refine lucas_primality 7875475313 (3 : ZMod 7875475313) ?_ (fun q hq hd => ?_)
  · rw [show 7875475313 - 1 = 7875475312 from by norm_num]
    reduce_mod_char
  · have e : 7875475313 - 1 = [2 ^ 4, 492217207 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7875475313 - 1) / 2 = 3937737656 from by norm_num]
      have h2 : (3 : ZMod 7875475313) ^ 3937737656 = ((7875475312 : ℕ) : ZMod 7875475313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_492217207).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7875475313 - 1) / 492217207 = 16 from by norm_num]
      have h2 : (3 : ZMod 7875475313) ^ 16 = ((43046721 : ℕ) : ZMod 7875475313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15092859525078825081684721 : Nat.Prime 15092859525078825081684721 := by
  refine lucas_primality 15092859525078825081684721 (13 : ZMod 15092859525078825081684721) ?_ (fun q hq hd => ?_)
  · rw [show 15092859525078825081684721 - 1 = 15092859525078825081684720 from by norm_num]
    reduce_mod_char
  · have e : 15092859525078825081684721 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 1, 17 ^ 1, 41 ^ 1, 383 ^ 1, 7753 ^ 1, 1171981 ^ 1, 8642057 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15092859525078825081684721 - 1) / 2 = 7546429762539412540842360 from by norm_num]
      have h2 : (13 : ZMod 15092859525078825081684721) ^ 7546429762539412540842360 = ((15092859525078825081684720 : ℕ) : ZMod 15092859525078825081684721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15092859525078825081684721 - 1) / 3 = 5030953175026275027228240 from by norm_num]
      have h2 : (13 : ZMod 15092859525078825081684721) ^ 5030953175026275027228240 = ((11242979085777978125768537 : ℕ) : ZMod 15092859525078825081684721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15092859525078825081684721 - 1) / 5 = 3018571905015765016336944 from by norm_num]
      have h2 : (13 : ZMod 15092859525078825081684721) ^ 3018571905015765016336944 = ((7528680598331038170986848 : ℕ) : ZMod 15092859525078825081684721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15092859525078825081684721 - 1) / 17 = 887815266181107357746160 from by norm_num]
      have h2 : (13 : ZMod 15092859525078825081684721) ^ 887815266181107357746160 = ((7951816781688134671499224 : ℕ) : ZMod 15092859525078825081684721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15092859525078825081684721 - 1) / 41 = 368118525001922562967920 from by norm_num]
      have h2 : (13 : ZMod 15092859525078825081684721) ^ 368118525001922562967920 = ((8494337118725441125157956 : ℕ) : ZMod 15092859525078825081684721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15092859525078825081684721 - 1) / 383 = 39406943929709726061840 from by norm_num]
      have h2 : (13 : ZMod 15092859525078825081684721) ^ 39406943929709726061840 = ((1361453900319334069315037 : ℕ) : ZMod 15092859525078825081684721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15092859525078825081684721 - 1) / 7753 = 1946712179166622608240 from by norm_num]
      have h2 : (13 : ZMod 15092859525078825081684721) ^ 1946712179166622608240 = ((2910331912294578730904399 : ℕ) : ZMod 15092859525078825081684721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15092859525078825081684721 - 1) / 1171981 = 12878075263232787120 from by norm_num]
      have h2 : (13 : ZMod 15092859525078825081684721) ^ 12878075263232787120 = ((8405679352123310777133752 : ℕ) : ZMod 15092859525078825081684721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15092859525078825081684721 - 1) / 8642057 = 1746442950454830960 from by norm_num]
      have h2 : (13 : ZMod 15092859525078825081684721) ^ 1746442950454830960 = ((10973436805176030949954124 : ℕ) : ZMod 15092859525078825081684721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1571511860719 : Nat.Prime 1571511860719 := by
  refine lucas_primality 1571511860719 (11 : ZMod 1571511860719) ?_ (fun q hq hd => ?_)
  · rw [show 1571511860719 - 1 = 1571511860718 from by norm_num]
    reduce_mod_char
  · have e : 1571511860719 - 1 = [2 ^ 1, 3 ^ 1, 103 ^ 1, 433 ^ 1, 977 ^ 1, 6011 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1571511860719 - 1) / 2 = 785755930359 from by norm_num]
      have h2 : (11 : ZMod 1571511860719) ^ 785755930359 = ((1571511860718 : ℕ) : ZMod 1571511860719) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1571511860719 - 1) / 3 = 523837286906 from by norm_num]
      have h2 : (11 : ZMod 1571511860719) ^ 523837286906 = ((1175564724041 : ℕ) : ZMod 1571511860719) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1571511860719 - 1) / 103 = 15257396706 from by norm_num]
      have h2 : (11 : ZMod 1571511860719) ^ 15257396706 = ((232608076322 : ℕ) : ZMod 1571511860719) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1571511860719 - 1) / 433 = 3629357646 from by norm_num]
      have h2 : (11 : ZMod 1571511860719) ^ 3629357646 = ((73052503954 : ℕ) : ZMod 1571511860719) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1571511860719 - 1) / 977 = 1608507534 from by norm_num]
      have h2 : (11 : ZMod 1571511860719) ^ 1608507534 = ((739783960724 : ℕ) : ZMod 1571511860719) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1571511860719 - 1) / 6011 = 261439338 from by norm_num]
      have h2 : (11 : ZMod 1571511860719) ^ 261439338 = ((1565067846602 : ℕ) : ZMod 1571511860719) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_97154822801 : Nat.Prime 97154822801 := by
  refine lucas_primality 97154822801 (3 : ZMod 97154822801) ?_ (fun q hq hd => ?_)
  · rw [show 97154822801 - 1 = 97154822800 from by norm_num]
    reduce_mod_char
  · have e : 97154822801 - 1 = [2 ^ 4, 5 ^ 2, 7 ^ 1, 34698151 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97154822801 - 1) / 2 = 48577411400 from by norm_num]
      have h2 : (3 : ZMod 97154822801) ^ 48577411400 = ((97154822800 : ℕ) : ZMod 97154822801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97154822801 - 1) / 5 = 19430964560 from by norm_num]
      have h2 : (3 : ZMod 97154822801) ^ 19430964560 = ((69487052630 : ℕ) : ZMod 97154822801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97154822801 - 1) / 7 = 13879260400 from by norm_num]
      have h2 : (3 : ZMod 97154822801) ^ 13879260400 = ((45377070766 : ℕ) : ZMod 97154822801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97154822801 - 1) / 34698151 = 2800 from by norm_num]
      have h2 : (3 : ZMod 97154822801) ^ 2800 = ((84628094167 : ℕ) : ZMod 97154822801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_34714989264498225976453201 : Nat.Prime 34714989264498225976453201 := by
  refine lucas_primality 34714989264498225976453201 (13 : ZMod 34714989264498225976453201) ?_ (fun q hq hd => ?_)
  · rw [show 34714989264498225976453201 - 1 = 34714989264498225976453200 from by norm_num]
    reduce_mod_char
  · have e : 34714989264498225976453201 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 2, 17 ^ 1, 29 ^ 1, 97 ^ 1, 157 ^ 1, 283 ^ 1, 317 ^ 1, 18257 ^ 1, 2352569 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34714989264498225976453201 - 1) / 2 = 17357494632249112988226600 from by norm_num]
      have h2 : (13 : ZMod 34714989264498225976453201) ^ 17357494632249112988226600 = ((34714989264498225976453200 : ℕ) : ZMod 34714989264498225976453201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34714989264498225976453201 - 1) / 3 = 11571663088166075325484400 from by norm_num]
      have h2 : (13 : ZMod 34714989264498225976453201) ^ 11571663088166075325484400 = ((10099981508292588533680532 : ℕ) : ZMod 34714989264498225976453201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34714989264498225976453201 - 1) / 5 = 6942997852899645195290640 from by norm_num]
      have h2 : (13 : ZMod 34714989264498225976453201) ^ 6942997852899645195290640 = ((15888757456745343784564047 : ℕ) : ZMod 34714989264498225976453201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34714989264498225976453201 - 1) / 17 = 2042058192029307410379600 from by norm_num]
      have h2 : (13 : ZMod 34714989264498225976453201) ^ 2042058192029307410379600 = ((3271766400211544452985475 : ℕ) : ZMod 34714989264498225976453201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34714989264498225976453201 - 1) / 29 = 1197068595327525033670800 from by norm_num]
      have h2 : (13 : ZMod 34714989264498225976453201) ^ 1197068595327525033670800 = ((19714793806984554599938025 : ℕ) : ZMod 34714989264498225976453201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34714989264498225976453201 - 1) / 97 = 357886487262868309035600 from by norm_num]
      have h2 : (13 : ZMod 34714989264498225976453201) ^ 357886487262868309035600 = ((20809202033610619633594171 : ℕ) : ZMod 34714989264498225976453201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34714989264498225976453201 - 1) / 157 = 221114581302536471187600 from by norm_num]
      have h2 : (13 : ZMod 34714989264498225976453201) ^ 221114581302536471187600 = ((12932980247656305479756323 : ℕ) : ZMod 34714989264498225976453201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34714989264498225976453201 - 1) / 283 = 122667806588332953980400 from by norm_num]
      have h2 : (13 : ZMod 34714989264498225976453201) ^ 122667806588332953980400 = ((21791223462470931658734777 : ℕ) : ZMod 34714989264498225976453201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34714989264498225976453201 - 1) / 317 = 109511007143527526739600 from by norm_num]
      have h2 : (13 : ZMod 34714989264498225976453201) ^ 109511007143527526739600 = ((8564626202966537261090480 : ℕ) : ZMod 34714989264498225976453201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34714989264498225976453201 - 1) / 18257 = 1901461864736716107600 from by norm_num]
      have h2 : (13 : ZMod 34714989264498225976453201) ^ 1901461864736716107600 = ((10690900381480917898728163 : ℕ) : ZMod 34714989264498225976453201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34714989264498225976453201 - 1) / 2352569 = 14756204500058542800 from by norm_num]
      have h2 : (13 : ZMod 34714989264498225976453201) ^ 14756204500058542800 = ((20477223021294096717403411 : ℕ) : ZMod 34714989264498225976453201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_39064015937 : Nat.Prime 39064015937 := by
  refine lucas_primality 39064015937 (3 : ZMod 39064015937) ?_ (fun q hq hd => ?_)
  · rw [show 39064015937 - 1 = 39064015936 from by norm_num]
    reduce_mod_char
  · have e : 39064015937 - 1 = [2 ^ 6, 11 ^ 1, 283 ^ 1, 196073 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39064015937 - 1) / 2 = 19532007968 from by norm_num]
      have h2 : (3 : ZMod 39064015937) ^ 19532007968 = ((39064015936 : ℕ) : ZMod 39064015937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39064015937 - 1) / 11 = 3551274176 from by norm_num]
      have h2 : (3 : ZMod 39064015937) ^ 3551274176 = ((17769310426 : ℕ) : ZMod 39064015937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39064015937 - 1) / 283 = 138035392 from by norm_num]
      have h2 : (3 : ZMod 39064015937) ^ 138035392 = ((7533516646 : ℕ) : ZMod 39064015937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39064015937 - 1) / 196073 = 199232 from by norm_num]
      have h2 : (3 : ZMod 39064015937) ^ 199232 = ((30233161185 : ℕ) : ZMod 39064015937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_887369321 : Nat.Prime 887369321 := by
  refine lucas_primality 887369321 (3 : ZMod 887369321) ?_ (fun q hq hd => ?_)
  · rw [show 887369321 - 1 = 887369320 from by norm_num]
    reduce_mod_char
  · have e : 887369321 - 1 = [2 ^ 3, 5 ^ 1, 127 ^ 1, 174679 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (887369321 - 1) / 2 = 443684660 from by norm_num]
      have h2 : (3 : ZMod 887369321) ^ 443684660 = ((887369320 : ℕ) : ZMod 887369321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (887369321 - 1) / 5 = 177473864 from by norm_num]
      have h2 : (3 : ZMod 887369321) ^ 177473864 = ((766235785 : ℕ) : ZMod 887369321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (887369321 - 1) / 127 = 6987160 from by norm_num]
      have h2 : (3 : ZMod 887369321) ^ 6987160 = ((834208373 : ℕ) : ZMod 887369321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (887369321 - 1) / 174679 = 5080 from by norm_num]
      have h2 : (3 : ZMod 887369321) ^ 5080 = ((599871620 : ℕ) : ZMod 887369321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_44588753651715539427437281 : Nat.Prime 44588753651715539427437281 := by
  refine lucas_primality 44588753651715539427437281 (7 : ZMod 44588753651715539427437281) ?_ (fun q hq hd => ?_)
  · rw [show 44588753651715539427437281 - 1 = 44588753651715539427437280 from by norm_num]
    reduce_mod_char
  · have e : 44588753651715539427437281 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 17 ^ 1, 73 ^ 1, 313 ^ 1, 877 ^ 1, 307301 ^ 1, 887369321 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44588753651715539427437281 - 1) / 2 = 22294376825857769713718640 from by norm_num]
      have h2 : (7 : ZMod 44588753651715539427437281) ^ 22294376825857769713718640 = ((44588753651715539427437280 : ℕ) : ZMod 44588753651715539427437281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44588753651715539427437281 - 1) / 3 = 14862917883905179809145760 from by norm_num]
      have h2 : (7 : ZMod 44588753651715539427437281) ^ 14862917883905179809145760 = ((26384985227716738140783357 : ℕ) : ZMod 44588753651715539427437281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44588753651715539427437281 - 1) / 5 = 8917750730343107885487456 from by norm_num]
      have h2 : (7 : ZMod 44588753651715539427437281) ^ 8917750730343107885487456 = ((7807850307470586220699957 : ℕ) : ZMod 44588753651715539427437281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44588753651715539427437281 - 1) / 17 = 2622867861865619966319840 from by norm_num]
      have h2 : (7 : ZMod 44588753651715539427437281) ^ 2622867861865619966319840 = ((14678191221855118804027730 : ℕ) : ZMod 44588753651715539427437281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44588753651715539427437281 - 1) / 73 = 610804844544048485307360 from by norm_num]
      have h2 : (7 : ZMod 44588753651715539427437281) ^ 610804844544048485307360 = ((12435701199191587923074098 : ℕ) : ZMod 44588753651715539427437281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44588753651715539427437281 - 1) / 313 = 142456081954362745774560 from by norm_num]
      have h2 : (7 : ZMod 44588753651715539427437281) ^ 142456081954362745774560 = ((10827872632270917114309325 : ℕ) : ZMod 44588753651715539427437281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44588753651715539427437281 - 1) / 877 = 50842364483142006188640 from by norm_num]
      have h2 : (7 : ZMod 44588753651715539427437281) ^ 50842364483142006188640 = ((2591770570846223719153502 : ℕ) : ZMod 44588753651715539427437281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44588753651715539427437281 - 1) / 307301 = 145097977721242493280 from by norm_num]
      have h2 : (7 : ZMod 44588753651715539427437281) ^ 145097977721242493280 = ((9870518629974292464740708 : ℕ) : ZMod 44588753651715539427437281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_887369321).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44588753651715539427437281 - 1) / 887369321 = 50248247935219680 from by norm_num]
      have h2 : (7 : ZMod 44588753651715539427437281) ^ 50248247935219680 = ((23084410912367260548176645 : ℕ) : ZMod 44588753651715539427437281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7152978793 : Nat.Prime 7152978793 := by
  refine lucas_primality 7152978793 (5 : ZMod 7152978793) ?_ (fun q hq hd => ?_)
  · rw [show 7152978793 - 1 = 7152978792 from by norm_num]
    reduce_mod_char
  · have e : 7152978793 - 1 = [2 ^ 3, 3 ^ 1, 19 ^ 1, 43 ^ 1, 53 ^ 1, 6883 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7152978793 - 1) / 2 = 3576489396 from by norm_num]
      have h2 : (5 : ZMod 7152978793) ^ 3576489396 = ((7152978792 : ℕ) : ZMod 7152978793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7152978793 - 1) / 3 = 2384326264 from by norm_num]
      have h2 : (5 : ZMod 7152978793) ^ 2384326264 = ((5969035372 : ℕ) : ZMod 7152978793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7152978793 - 1) / 19 = 376472568 from by norm_num]
      have h2 : (5 : ZMod 7152978793) ^ 376472568 = ((5284203782 : ℕ) : ZMod 7152978793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7152978793 - 1) / 43 = 166348344 from by norm_num]
      have h2 : (5 : ZMod 7152978793) ^ 166348344 = ((1619771549 : ℕ) : ZMod 7152978793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7152978793 - 1) / 53 = 134961864 from by norm_num]
      have h2 : (5 : ZMod 7152978793) ^ 134961864 = ((794149277 : ℕ) : ZMod 7152978793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7152978793 - 1) / 6883 = 1039224 from by norm_num]
      have h2 : (5 : ZMod 7152978793) ^ 1039224 = ((3546611745 : ℕ) : ZMod 7152978793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_49712937585586541809314241 : Nat.Prime 49712937585586541809314241 := by
  refine lucas_primality 49712937585586541809314241 (22 : ZMod 49712937585586541809314241) ?_ (fun q hq hd => ?_)
  · rw [show 49712937585586541809314241 - 1 = 49712937585586541809314240 from by norm_num]
    reduce_mod_char
  · have e : 49712937585586541809314241 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 37 ^ 1, 41 ^ 1, 109 ^ 1, 127 ^ 1, 2897 ^ 1, 7152978793 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49712937585586541809314241 - 1) / 2 = 24856468792793270904657120 from by norm_num]
      have h2 : (22 : ZMod 49712937585586541809314241) ^ 24856468792793270904657120 = ((49712937585586541809314240 : ℕ) : ZMod 49712937585586541809314241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49712937585586541809314241 - 1) / 3 = 16570979195195513936438080 from by norm_num]
      have h2 : (22 : ZMod 49712937585586541809314241) ^ 16570979195195513936438080 = ((44922939733950679930879418 : ℕ) : ZMod 49712937585586541809314241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49712937585586541809314241 - 1) / 5 = 9942587517117308361862848 from by norm_num]
      have h2 : (22 : ZMod 49712937585586541809314241) ^ 9942587517117308361862848 = ((22363739480806215686955308 : ℕ) : ZMod 49712937585586541809314241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49712937585586541809314241 - 1) / 7 = 7101848226512363115616320 from by norm_num]
      have h2 : (22 : ZMod 49712937585586541809314241) ^ 7101848226512363115616320 = ((16089424733200065716527881 : ℕ) : ZMod 49712937585586541809314241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49712937585586541809314241 - 1) / 17 = 2924290446210973047606720 from by norm_num]
      have h2 : (22 : ZMod 49712937585586541809314241) ^ 2924290446210973047606720 = ((211677471177316327030401 : ℕ) : ZMod 49712937585586541809314241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49712937585586541809314241 - 1) / 37 = 1343592907718555184035520 from by norm_num]
      have h2 : (22 : ZMod 49712937585586541809314241) ^ 1343592907718555184035520 = ((34603972914315220522695469 : ℕ) : ZMod 49712937585586541809314241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49712937585586541809314241 - 1) / 41 = 1212510672819183946568640 from by norm_num]
      have h2 : (22 : ZMod 49712937585586541809314241) ^ 1212510672819183946568640 = ((44019930465148314811634358 : ℕ) : ZMod 49712937585586541809314241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49712937585586541809314241 - 1) / 109 = 456081996198041667975360 from by norm_num]
      have h2 : (22 : ZMod 49712937585586541809314241) ^ 456081996198041667975360 = ((36666491220745465745564651 : ℕ) : ZMod 49712937585586541809314241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49712937585586541809314241 - 1) / 127 = 391440453429815289837120 from by norm_num]
      have h2 : (22 : ZMod 49712937585586541809314241) ^ 391440453429815289837120 = ((14198022904006748064501735 : ℕ) : ZMod 49712937585586541809314241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49712937585586541809314241 - 1) / 2897 = 17160144144144474217920 from by norm_num]
      have h2 : (22 : ZMod 49712937585586541809314241) ^ 17160144144144474217920 = ((28358523021651218378141911 : ℕ) : ZMod 49712937585586541809314241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_7152978793).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49712937585586541809314241 - 1) / 7152978793 = 6949962948895680 from by norm_num]
      have h2 : (22 : ZMod 49712937585586541809314241) ^ 6949962948895680 = ((30821527047556548217997107 : ℕ) : ZMod 49712937585586541809314241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3452552017 : Nat.Prime 3452552017 := by
  refine lucas_primality 3452552017 (7 : ZMod 3452552017) ?_ (fun q hq hd => ?_)
  · rw [show 3452552017 - 1 = 3452552016 from by norm_num]
    reduce_mod_char
  · have e : 3452552017 - 1 = [2 ^ 4, 3 ^ 1, 19 ^ 2, 199247 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3452552017 - 1) / 2 = 1726276008 from by norm_num]
      have h2 : (7 : ZMod 3452552017) ^ 1726276008 = ((3452552016 : ℕ) : ZMod 3452552017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3452552017 - 1) / 3 = 1150850672 from by norm_num]
      have h2 : (7 : ZMod 3452552017) ^ 1150850672 = ((251894622 : ℕ) : ZMod 3452552017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3452552017 - 1) / 19 = 181713264 from by norm_num]
      have h2 : (7 : ZMod 3452552017) ^ 181713264 = ((3085815328 : ℕ) : ZMod 3452552017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3452552017 - 1) / 199247 = 17328 from by norm_num]
      have h2 : (7 : ZMod 3452552017) ^ 17328 = ((3260235922 : ℕ) : ZMod 3452552017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1726276009 : Nat.Prime 1726276009 := by
  refine lucas_primality 1726276009 (7 : ZMod 1726276009) ?_ (fun q hq hd => ?_)
  · rw [show 1726276009 - 1 = 1726276008 from by norm_num]
    reduce_mod_char
  · have e : 1726276009 - 1 = [2 ^ 3, 3 ^ 1, 19 ^ 2, 199247 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1726276009 - 1) / 2 = 863138004 from by norm_num]
      have h2 : (7 : ZMod 1726276009) ^ 863138004 = ((1726276008 : ℕ) : ZMod 1726276009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1726276009 - 1) / 3 = 575425336 from by norm_num]
      have h2 : (7 : ZMod 1726276009) ^ 575425336 = ((48085376 : ℕ) : ZMod 1726276009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1726276009 - 1) / 19 = 90856632 from by norm_num]
      have h2 : (7 : ZMod 1726276009) ^ 90856632 = ((654560651 : ℕ) : ZMod 1726276009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1726276009 - 1) / 199247 = 8664 from by norm_num]
      have h2 : (7 : ZMod 1726276009) ^ 8664 = ((1307265353 : ℕ) : ZMod 1726276009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1861745233 : Nat.Prime 1861745233 := by
  refine lucas_primality 1861745233 (5 : ZMod 1861745233) ?_ (fun q hq hd => ?_)
  · rw [show 1861745233 - 1 = 1861745232 from by norm_num]
    reduce_mod_char
  · have e : 1861745233 - 1 = [2 ^ 4, 3 ^ 1, 2777 ^ 1, 13967 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1861745233 - 1) / 2 = 930872616 from by norm_num]
      have h2 : (5 : ZMod 1861745233) ^ 930872616 = ((1861745232 : ℕ) : ZMod 1861745233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1861745233 - 1) / 3 = 620581744 from by norm_num]
      have h2 : (5 : ZMod 1861745233) ^ 620581744 = ((1514443192 : ℕ) : ZMod 1861745233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1861745233 - 1) / 2777 = 670416 from by norm_num]
      have h2 : (5 : ZMod 1861745233) ^ 670416 = ((21300364 : ℕ) : ZMod 1861745233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1861745233 - 1) / 13967 = 133296 from by norm_num]
      have h2 : (5 : ZMod 1861745233) ^ 133296 = ((762088630 : ℕ) : ZMod 1861745233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_75086230851720457458598081 : Nat.Prime 75086230851720457458598081 := by
  refine lucas_primality 75086230851720457458598081 (29 : ZMod 75086230851720457458598081) ?_ (fun q hq hd => ?_)
  · rw [show 75086230851720457458598081 - 1 = 75086230851720457458598080 from by norm_num]
    reduce_mod_char
  · have e : 75086230851720457458598081 - 1 = [2 ^ 6, 3 ^ 2, 5 ^ 1, 11 ^ 1, 13 ^ 1, 17 ^ 1, 73 ^ 1, 23977 ^ 1, 1873513 ^ 1, 3270457 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75086230851720457458598081 - 1) / 2 = 37543115425860228729299040 from by norm_num]
      have h2 : (29 : ZMod 75086230851720457458598081) ^ 37543115425860228729299040 = ((75086230851720457458598080 : ℕ) : ZMod 75086230851720457458598081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75086230851720457458598081 - 1) / 3 = 25028743617240152486199360 from by norm_num]
      have h2 : (29 : ZMod 75086230851720457458598081) ^ 25028743617240152486199360 = ((50164892047715565924783884 : ℕ) : ZMod 75086230851720457458598081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75086230851720457458598081 - 1) / 5 = 15017246170344091491719616 from by norm_num]
      have h2 : (29 : ZMod 75086230851720457458598081) ^ 15017246170344091491719616 = ((59575252897564766635536151 : ℕ) : ZMod 75086230851720457458598081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75086230851720457458598081 - 1) / 11 = 6826020986520041587145280 from by norm_num]
      have h2 : (29 : ZMod 75086230851720457458598081) ^ 6826020986520041587145280 = ((37974470453851736091465826 : ℕ) : ZMod 75086230851720457458598081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75086230851720457458598081 - 1) / 13 = 5775863911670804419892160 from by norm_num]
      have h2 : (29 : ZMod 75086230851720457458598081) ^ 5775863911670804419892160 = ((44400832531295167583570123 : ℕ) : ZMod 75086230851720457458598081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75086230851720457458598081 - 1) / 17 = 4416837108924732791682240 from by norm_num]
      have h2 : (29 : ZMod 75086230851720457458598081) ^ 4416837108924732791682240 = ((20867501348573158156921801 : ℕ) : ZMod 75086230851720457458598081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75086230851720457458598081 - 1) / 73 = 1028578504818088458336960 from by norm_num]
      have h2 : (29 : ZMod 75086230851720457458598081) ^ 1028578504818088458336960 = ((21473227190888840674861067 : ℕ) : ZMod 75086230851720457458598081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75086230851720457458598081 - 1) / 23977 = 3131594063132187407040 from by norm_num]
      have h2 : (29 : ZMod 75086230851720457458598081) ^ 3131594063132187407040 = ((70557377107474270706553817 : ℕ) : ZMod 75086230851720457458598081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75086230851720457458598081 - 1) / 1873513 = 40077774134324372160 from by norm_num]
      have h2 : (29 : ZMod 75086230851720457458598081) ^ 40077774134324372160 = ((44680659743683608221626814 : ℕ) : ZMod 75086230851720457458598081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75086230851720457458598081 - 1) / 3270457 = 22958941472620021440 from by norm_num]
      have h2 : (29 : ZMod 75086230851720457458598081) ^ 22958941472620021440 = ((21514812229647093314914045 : ℕ) : ZMod 75086230851720457458598081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_262198292243137 : Nat.Prime 262198292243137 := by
  refine lucas_primality 262198292243137 (7 : ZMod 262198292243137) ?_ (fun q hq hd => ?_)
  · rw [show 262198292243137 - 1 = 262198292243136 from by norm_num]
    reduce_mod_char
  · have e : 262198292243137 - 1 = [2 ^ 6, 3 ^ 1, 3709 ^ 1, 7841 ^ 1, 46957 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (262198292243137 - 1) / 2 = 131099146121568 from by norm_num]
      have h2 : (7 : ZMod 262198292243137) ^ 131099146121568 = ((262198292243136 : ℕ) : ZMod 262198292243137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (262198292243137 - 1) / 3 = 87399430747712 from by norm_num]
      have h2 : (7 : ZMod 262198292243137) ^ 87399430747712 = ((66596404882164 : ℕ) : ZMod 262198292243137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (262198292243137 - 1) / 3709 = 70692448704 from by norm_num]
      have h2 : (7 : ZMod 262198292243137) ^ 70692448704 = ((120548217904032 : ℕ) : ZMod 262198292243137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (262198292243137 - 1) / 7841 = 33439394496 from by norm_num]
      have h2 : (7 : ZMod 262198292243137) ^ 33439394496 = ((229106712462555 : ℕ) : ZMod 262198292243137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (262198292243137 - 1) / 46957 = 5583795648 from by norm_num]
      have h2 : (7 : ZMod 262198292243137) ^ 5583795648 = ((45460620977261 : ℕ) : ZMod 262198292243137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_292083232917564916412257 : Nat.Prime 292083232917564916412257 := by
  refine lucas_primality 292083232917564916412257 (10 : ZMod 292083232917564916412257) ?_ (fun q hq hd => ?_)
  · rw [show 292083232917564916412257 - 1 = 292083232917564916412256 from by norm_num]
    reduce_mod_char
  · have e : 292083232917564916412257 - 1 = [2 ^ 5, 3 ^ 4, 7 ^ 2, 251 ^ 1, 1301 ^ 1, 2377 ^ 1, 13831 ^ 1, 214211 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292083232917564916412257 - 1) / 2 = 146041616458782458206128 from by norm_num]
      have h2 : (10 : ZMod 292083232917564916412257) ^ 146041616458782458206128 = ((292083232917564916412256 : ℕ) : ZMod 292083232917564916412257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292083232917564916412257 - 1) / 3 = 97361077639188305470752 from by norm_num]
      have h2 : (10 : ZMod 292083232917564916412257) ^ 97361077639188305470752 = ((241159873560980868056283 : ℕ) : ZMod 292083232917564916412257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292083232917564916412257 - 1) / 7 = 41726176131080702344608 from by norm_num]
      have h2 : (10 : ZMod 292083232917564916412257) ^ 41726176131080702344608 = ((196311791142205818153155 : ℕ) : ZMod 292083232917564916412257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292083232917564916412257 - 1) / 251 = 1163678218795079348256 from by norm_num]
      have h2 : (10 : ZMod 292083232917564916412257) ^ 1163678218795079348256 = ((239145095492924710542334 : ℕ) : ZMod 292083232917564916412257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292083232917564916412257 - 1) / 1301 = 224506712465461119456 from by norm_num]
      have h2 : (10 : ZMod 292083232917564916412257) ^ 224506712465461119456 = ((157332845536231998811326 : ℕ) : ZMod 292083232917564916412257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292083232917564916412257 - 1) / 2377 = 122878936860565804128 from by norm_num]
      have h2 : (10 : ZMod 292083232917564916412257) ^ 122878936860565804128 = ((154182975208697792581639 : ℕ) : ZMod 292083232917564916412257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292083232917564916412257 - 1) / 13831 = 21118012646776438176 from by norm_num]
      have h2 : (10 : ZMod 292083232917564916412257) ^ 21118012646776438176 = ((36660686025541370400129 : ℕ) : ZMod 292083232917564916412257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292083232917564916412257 - 1) / 214211 = 1363530504584568096 from by norm_num]
      have h2 : (10 : ZMod 292083232917564916412257) ^ 1363530504584568096 = ((169205819322008764270862 : ℕ) : ZMod 292083232917564916412257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_214736371 : Nat.Prime 214736371 := by
  refine lucas_primality 214736371 (11 : ZMod 214736371) ?_ (fun q hq hd => ?_)
  · rw [show 214736371 - 1 = 214736370 from by norm_num]
    reduce_mod_char
  · have e : 214736371 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 7157879 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (214736371 - 1) / 2 = 107368185 from by norm_num]
      have h2 : (11 : ZMod 214736371) ^ 107368185 = ((214736370 : ℕ) : ZMod 214736371) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (214736371 - 1) / 3 = 71578790 from by norm_num]
      have h2 : (11 : ZMod 214736371) ^ 71578790 = ((164763038 : ℕ) : ZMod 214736371) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (214736371 - 1) / 5 = 42947274 from by norm_num]
      have h2 : (11 : ZMod 214736371) ^ 42947274 = ((95950517 : ℕ) : ZMod 214736371) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (214736371 - 1) / 7157879 = 30 from by norm_num]
      have h2 : (11 : ZMod 214736371) ^ 30 = ((81678947 : ℕ) : ZMod 214736371) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_157790771387783474187901681 : Nat.Prime 157790771387783474187901681 := by
  refine lucas_primality 157790771387783474187901681 (46 : ZMod 157790771387783474187901681) ?_ (fun q hq hd => ?_)
  · rw [show 157790771387783474187901681 - 1 = 157790771387783474187901680 from by norm_num]
    reduce_mod_char
  · have e : 157790771387783474187901681 - 1 = [2 ^ 4, 3 ^ 3, 5 ^ 1, 13 ^ 1, 17 ^ 1, 19 ^ 1, 41 ^ 1, 79 ^ 1, 24793 ^ 1, 216641645201 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (157790771387783474187901681 - 1) / 2 = 78895385693891737093950840 from by norm_num]
      have h2 : (46 : ZMod 157790771387783474187901681) ^ 78895385693891737093950840 = ((157790771387783474187901680 : ℕ) : ZMod 157790771387783474187901681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (157790771387783474187901681 - 1) / 3 = 52596923795927824729300560 from by norm_num]
      have h2 : (46 : ZMod 157790771387783474187901681) ^ 52596923795927824729300560 = ((128795136153219986079706857 : ℕ) : ZMod 157790771387783474187901681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (157790771387783474187901681 - 1) / 5 = 31558154277556694837580336 from by norm_num]
      have h2 : (46 : ZMod 157790771387783474187901681) ^ 31558154277556694837580336 = ((36671248266588331074577248 : ℕ) : ZMod 157790771387783474187901681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (157790771387783474187901681 - 1) / 13 = 12137751645214113399069360 from by norm_num]
      have h2 : (46 : ZMod 157790771387783474187901681) ^ 12137751645214113399069360 = ((2271995413202934410189180 : ℕ) : ZMod 157790771387783474187901681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (157790771387783474187901681 - 1) / 17 = 9281810081634322011053040 from by norm_num]
      have h2 : (46 : ZMod 157790771387783474187901681) ^ 9281810081634322011053040 = ((5966810128202699781002737 : ℕ) : ZMod 157790771387783474187901681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (157790771387783474187901681 - 1) / 19 = 8304777441462288115152720 from by norm_num]
      have h2 : (46 : ZMod 157790771387783474187901681) ^ 8304777441462288115152720 = ((117506119145486799983484895 : ℕ) : ZMod 157790771387783474187901681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (157790771387783474187901681 - 1) / 41 = 3848555399702035955802480 from by norm_num]
      have h2 : (46 : ZMod 157790771387783474187901681) ^ 3848555399702035955802480 = ((102738287985453238282466992 : ℕ) : ZMod 157790771387783474187901681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (157790771387783474187901681 - 1) / 79 = 1997351536554221192251920 from by norm_num]
      have h2 : (46 : ZMod 157790771387783474187901681) ^ 1997351536554221192251920 = ((110893397454494339645860817 : ℕ) : ZMod 157790771387783474187901681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (157790771387783474187901681 - 1) / 24793 = 6364327487104564763760 from by norm_num]
      have h2 : (46 : ZMod 157790771387783474187901681) ^ 6364327487104564763760 = ((127901076745872497519675346 : ℕ) : ZMod 157790771387783474187901681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_216641645201).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (157790771387783474187901681 - 1) / 216641645201 = 728349211165680 from by norm_num]
      have h2 : (46 : ZMod 157790771387783474187901681) ^ 728349211165680 = ((155576231510888710411160007 : ℕ) : ZMod 157790771387783474187901681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_822740921 : Nat.Prime 822740921 := by
  refine lucas_primality 822740921 (3 : ZMod 822740921) ?_ (fun q hq hd => ?_)
  · rw [show 822740921 - 1 = 822740920 from by norm_num]
    reduce_mod_char
  · have e : 822740921 - 1 = [2 ^ 3, 5 ^ 1, 89 ^ 1, 231107 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (822740921 - 1) / 2 = 411370460 from by norm_num]
      have h2 : (3 : ZMod 822740921) ^ 411370460 = ((822740920 : ℕ) : ZMod 822740921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (822740921 - 1) / 5 = 164548184 from by norm_num]
      have h2 : (3 : ZMod 822740921) ^ 164548184 = ((549461922 : ℕ) : ZMod 822740921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (822740921 - 1) / 89 = 9244280 from by norm_num]
      have h2 : (3 : ZMod 822740921) ^ 9244280 = ((561153394 : ℕ) : ZMod 822740921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (822740921 - 1) / 231107 = 3560 from by norm_num]
      have h2 : (3 : ZMod 822740921) ^ 3560 = ((522657209 : ℕ) : ZMod 822740921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_177208342683739494697085521 : Nat.Prime 177208342683739494697085521 := by
  refine lucas_primality 177208342683739494697085521 (13 : ZMod 177208342683739494697085521) ?_ (fun q hq hd => ?_)
  · rw [show 177208342683739494697085521 - 1 = 177208342683739494697085520 from by norm_num]
    reduce_mod_char
  · have e : 177208342683739494697085521 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 17 ^ 1, 347 ^ 1, 521 ^ 1, 673 ^ 1, 433889 ^ 1, 822740921 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (177208342683739494697085521 - 1) / 2 = 88604171341869747348542760 from by norm_num]
      have h2 : (13 : ZMod 177208342683739494697085521) ^ 88604171341869747348542760 = ((177208342683739494697085520 : ℕ) : ZMod 177208342683739494697085521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (177208342683739494697085521 - 1) / 3 = 59069447561246498232361840 from by norm_num]
      have h2 : (13 : ZMod 177208342683739494697085521) ^ 59069447561246498232361840 = ((675241973361197185877318 : ℕ) : ZMod 177208342683739494697085521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (177208342683739494697085521 - 1) / 5 = 35441668536747898939417104 from by norm_num]
      have h2 : (13 : ZMod 177208342683739494697085521) ^ 35441668536747898939417104 = ((154180442698008285557467177 : ℕ) : ZMod 177208342683739494697085521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (177208342683739494697085521 - 1) / 17 = 10424020157867029099828560 from by norm_num]
      have h2 : (13 : ZMod 177208342683739494697085521) ^ 10424020157867029099828560 = ((98198043403505692725270366 : ℕ) : ZMod 177208342683739494697085521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (177208342683739494697085521 - 1) / 347 = 510686866523744941490160 from by norm_num]
      have h2 : (13 : ZMod 177208342683739494697085521) ^ 510686866523744941490160 = ((69396127806186637473236569 : ℕ) : ZMod 177208342683739494697085521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (177208342683739494697085521 - 1) / 521 = 340131175976467360263120 from by norm_num]
      have h2 : (13 : ZMod 177208342683739494697085521) ^ 340131175976467360263120 = ((69981351834155286567383508 : ℕ) : ZMod 177208342683739494697085521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (177208342683739494697085521 - 1) / 673 = 263311058965437584988240 from by norm_num]
      have h2 : (13 : ZMod 177208342683739494697085521) ^ 263311058965437584988240 = ((47828478854521729485635670 : ℕ) : ZMod 177208342683739494697085521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (177208342683739494697085521 - 1) / 433889 = 408418610943673369680 from by norm_num]
      have h2 : (13 : ZMod 177208342683739494697085521) ^ 408418610943673369680 = ((91172202644042177920507970 : ℕ) : ZMod 177208342683739494697085521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_822740921).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (177208342683739494697085521 - 1) / 822740921 = 215387782667175120 from by norm_num]
      have h2 : (13 : ZMod 177208342683739494697085521) ^ 215387782667175120 = ((152958629641469686898283034 : ℕ) : ZMod 177208342683739494697085521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_146844953 : Nat.Prime 146844953 := by
  refine lucas_primality 146844953 (3 : ZMod 146844953) ?_ (fun q hq hd => ?_)
  · rw [show 146844953 - 1 = 146844952 from by norm_num]
    reduce_mod_char
  · have e : 146844953 - 1 = [2 ^ 3, 2207 ^ 1, 8317 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146844953 - 1) / 2 = 73422476 from by norm_num]
      have h2 : (3 : ZMod 146844953) ^ 73422476 = ((146844952 : ℕ) : ZMod 146844953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146844953 - 1) / 2207 = 66536 from by norm_num]
      have h2 : (3 : ZMod 146844953) ^ 66536 = ((51826127 : ℕ) : ZMod 146844953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146844953 - 1) / 8317 = 17656 from by norm_num]
      have h2 : (3 : ZMod 146844953) ^ 17656 = ((44145537 : ℕ) : ZMod 146844953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_14102207757738301344667 : Nat.Prime 14102207757738301344667 := by
  refine lucas_primality 14102207757738301344667 (2 : ZMod 14102207757738301344667) ?_ (fun q hq hd => ?_)
  · rw [show 14102207757738301344667 - 1 = 14102207757738301344666 from by norm_num]
    reduce_mod_char
  · have e : 14102207757738301344667 - 1 = [2 ^ 1, 3 ^ 1, 19 ^ 1, 101 ^ 1, 8369 ^ 1, 996617 ^ 1, 146844953 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14102207757738301344667 - 1) / 2 = 7051103878869150672333 from by norm_num]
      have h2 : (2 : ZMod 14102207757738301344667) ^ 7051103878869150672333 = ((14102207757738301344666 : ℕ) : ZMod 14102207757738301344667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14102207757738301344667 - 1) / 3 = 4700735919246100448222 from by norm_num]
      have h2 : (2 : ZMod 14102207757738301344667) ^ 4700735919246100448222 = ((9412978877160 : ℕ) : ZMod 14102207757738301344667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14102207757738301344667 - 1) / 19 = 742221460933594807614 from by norm_num]
      have h2 : (2 : ZMod 14102207757738301344667) ^ 742221460933594807614 = ((11463514856404764106528 : ℕ) : ZMod 14102207757738301344667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14102207757738301344667 - 1) / 101 = 139625819383547538066 from by norm_num]
      have h2 : (2 : ZMod 14102207757738301344667) ^ 139625819383547538066 = ((860002731514019257552 : ℕ) : ZMod 14102207757738301344667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14102207757738301344667 - 1) / 8369 = 1685052904497347514 from by norm_num]
      have h2 : (2 : ZMod 14102207757738301344667) ^ 1685052904497347514 = ((9087046424170131318763 : ℕ) : ZMod 14102207757738301344667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14102207757738301344667 - 1) / 996617 = 14150077469818698 from by norm_num]
      have h2 : (2 : ZMod 14102207757738301344667) ^ 14150077469818698 = ((6489475046707793901520 : ℕ) : ZMod 14102207757738301344667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_146844953).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14102207757738301344667 - 1) / 146844953 = 96034677866922 from by norm_num]
      have h2 : (2 : ZMod 14102207757738301344667) ^ 96034677866922 = ((6210876543092564443790 : ℕ) : ZMod 14102207757738301344667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_365656673 : Nat.Prime 365656673 := by
  refine lucas_primality 365656673 (3 : ZMod 365656673) ?_ (fun q hq hd => ?_)
  · rw [show 365656673 - 1 = 365656672 from by norm_num]
    reduce_mod_char
  · have e : 365656673 - 1 = [2 ^ 5, 17 ^ 2, 19 ^ 1, 2081 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (365656673 - 1) / 2 = 182828336 from by norm_num]
      have h2 : (3 : ZMod 365656673) ^ 182828336 = ((365656672 : ℕ) : ZMod 365656673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (365656673 - 1) / 17 = 21509216 from by norm_num]
      have h2 : (3 : ZMod 365656673) ^ 21509216 = ((198022946 : ℕ) : ZMod 365656673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (365656673 - 1) / 19 = 19245088 from by norm_num]
      have h2 : (3 : ZMod 365656673) ^ 19245088 = ((235118405 : ℕ) : ZMod 365656673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (365656673 - 1) / 2081 = 175712 from by norm_num]
      have h2 : (3 : ZMod 365656673) ^ 175712 = ((65037274 : ℕ) : ZMod 365656673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_125123236840173674393761 : Nat.Prime 125123236840173674393761 := by
  refine lucas_primality 125123236840173674393761 (19 : ZMod 125123236840173674393761) ?_ (fun q hq hd => ?_)
  · rw [show 125123236840173674393761 - 1 = 125123236840173674393760 from by norm_num]
    reduce_mod_char
  · have e : 125123236840173674393761 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 421 ^ 1, 26209 ^ 1, 353641 ^ 1, 561377 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (125123236840173674393761 - 1) / 2 = 62561618420086837196880 from by norm_num]
      have h2 : (19 : ZMod 125123236840173674393761) ^ 62561618420086837196880 = ((125123236840173674393760 : ℕ) : ZMod 125123236840173674393761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (125123236840173674393761 - 1) / 3 = 41707745613391224797920 from by norm_num]
      have h2 : (19 : ZMod 125123236840173674393761) ^ 41707745613391224797920 = ((34261399082557599313153 : ℕ) : ZMod 125123236840173674393761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (125123236840173674393761 - 1) / 5 = 25024647368034734878752 from by norm_num]
      have h2 : (19 : ZMod 125123236840173674393761) ^ 25024647368034734878752 = ((2652668339038841486772 : ℕ) : ZMod 125123236840173674393761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (125123236840173674393761 - 1) / 7 = 17874748120024810627680 from by norm_num]
      have h2 : (19 : ZMod 125123236840173674393761) ^ 17874748120024810627680 = ((39919965706601901807961 : ℕ) : ZMod 125123236840173674393761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (125123236840173674393761 - 1) / 17 = 7360190402363157317280 from by norm_num]
      have h2 : (19 : ZMod 125123236840173674393761) ^ 7360190402363157317280 = ((37693437597732985874163 : ℕ) : ZMod 125123236840173674393761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (125123236840173674393761 - 1) / 421 = 297204838100174998560 from by norm_num]
      have h2 : (19 : ZMod 125123236840173674393761) ^ 297204838100174998560 = ((87109240504563653184533 : ℕ) : ZMod 125123236840173674393761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (125123236840173674393761 - 1) / 26209 = 4774056119660180640 from by norm_num]
      have h2 : (19 : ZMod 125123236840173674393761) ^ 4774056119660180640 = ((1837982988632397923539 : ℕ) : ZMod 125123236840173674393761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (125123236840173674393761 - 1) / 353641 = 353814282959763360 from by norm_num]
      have h2 : (19 : ZMod 125123236840173674393761) ^ 353814282959763360 = ((52610165946735413502728 : ℕ) : ZMod 125123236840173674393761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (125123236840173674393761 - 1) / 561377 = 222886290033566880 from by norm_num]
      have h2 : (19 : ZMod 125123236840173674393761) ^ 222886290033566880 = ((110549972413173428515165 : ℕ) : ZMod 125123236840173674393761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_136593761 : Nat.Prime 136593761 := by
  refine lucas_primality 136593761 (6 : ZMod 136593761) ?_ (fun q hq hd => ?_)
  · rw [show 136593761 - 1 = 136593760 from by norm_num]
    reduce_mod_char
  · have e : 136593761 - 1 = [2 ^ 5, 5 ^ 1, 487 ^ 1, 1753 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (136593761 - 1) / 2 = 68296880 from by norm_num]
      have h2 : (6 : ZMod 136593761) ^ 68296880 = ((136593760 : ℕ) : ZMod 136593761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (136593761 - 1) / 5 = 27318752 from by norm_num]
      have h2 : (6 : ZMod 136593761) ^ 27318752 = ((80192141 : ℕ) : ZMod 136593761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (136593761 - 1) / 487 = 280480 from by norm_num]
      have h2 : (6 : ZMod 136593761) ^ 280480 = ((120542026 : ℕ) : ZMod 136593761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (136593761 - 1) / 1753 = 77920 from by norm_num]
      have h2 : (6 : ZMod 136593761) ^ 77920 = ((79919750 : ℕ) : ZMod 136593761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1336981409 : Nat.Prime 1336981409 := by
  refine lucas_primality 1336981409 (3 : ZMod 1336981409) ?_ (fun q hq hd => ?_)
  · rw [show 1336981409 - 1 = 1336981408 from by norm_num]
    reduce_mod_char
  · have e : 1336981409 - 1 = [2 ^ 5, 7 ^ 1, 61 ^ 1, 97847 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1336981409 - 1) / 2 = 668490704 from by norm_num]
      have h2 : (3 : ZMod 1336981409) ^ 668490704 = ((1336981408 : ℕ) : ZMod 1336981409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1336981409 - 1) / 7 = 190997344 from by norm_num]
      have h2 : (3 : ZMod 1336981409) ^ 190997344 = ((355574520 : ℕ) : ZMod 1336981409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1336981409 - 1) / 61 = 21917728 from by norm_num]
      have h2 : (3 : ZMod 1336981409) ^ 21917728 = ((265799200 : ℕ) : ZMod 1336981409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1336981409 - 1) / 97847 = 13664 from by norm_num]
      have h2 : (3 : ZMod 1336981409) ^ 13664 = ((21228970 : ℕ) : ZMod 1336981409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_190404353 : Nat.Prime 190404353 := by
  refine lucas_primality 190404353 (3 : ZMod 190404353) ?_ (fun q hq hd => ?_)
  · rw [show 190404353 - 1 = 190404352 from by norm_num]
    reduce_mod_char
  · have e : 190404353 - 1 = [2 ^ 8, 17 ^ 1, 67 ^ 1, 653 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (190404353 - 1) / 2 = 95202176 from by norm_num]
      have h2 : (3 : ZMod 190404353) ^ 95202176 = ((190404352 : ℕ) : ZMod 190404353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (190404353 - 1) / 17 = 11200256 from by norm_num]
      have h2 : (3 : ZMod 190404353) ^ 11200256 = ((126221017 : ℕ) : ZMod 190404353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (190404353 - 1) / 67 = 2841856 from by norm_num]
      have h2 : (3 : ZMod 190404353) ^ 2841856 = ((188914315 : ℕ) : ZMod 190404353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (190404353 - 1) / 653 = 291584 from by norm_num]
      have h2 : (3 : ZMod 190404353) ^ 291584 = ((6739099 : ℕ) : ZMod 190404353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_80486459297 : Nat.Prime 80486459297 := by
  refine lucas_primality 80486459297 (3 : ZMod 80486459297) ?_ (fun q hq hd => ?_)
  · rw [show 80486459297 - 1 = 80486459296 from by norm_num]
    reduce_mod_char
  · have e : 80486459297 - 1 = [2 ^ 5, 127 ^ 1, 179 ^ 1, 110641 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (80486459297 - 1) / 2 = 40243229648 from by norm_num]
      have h2 : (3 : ZMod 80486459297) ^ 40243229648 = ((80486459296 : ℕ) : ZMod 80486459297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (80486459297 - 1) / 127 = 633751648 from by norm_num]
      have h2 : (3 : ZMod 80486459297) ^ 633751648 = ((22352075621 : ℕ) : ZMod 80486459297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (80486459297 - 1) / 179 = 449645024 from by norm_num]
      have h2 : (3 : ZMod 80486459297) ^ 449645024 = ((11907679212 : ℕ) : ZMod 80486459297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (80486459297 - 1) / 110641 = 727456 from by norm_num]
      have h2 : (3 : ZMod 80486459297) ^ 727456 = ((58061326552 : ℕ) : ZMod 80486459297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_18220998304703819917441 : Nat.Prime 18220998304703819917441 := by
  refine lucas_primality 18220998304703819917441 (13 : ZMod 18220998304703819917441) ?_ (fun q hq hd => ?_)
  · rw [show 18220998304703819917441 - 1 = 18220998304703819917440 from by norm_num]
    reduce_mod_char
  · have e : 18220998304703819917441 - 1 = [2 ^ 7, 3 ^ 2, 5 ^ 1, 23 ^ 1, 157 ^ 1, 167 ^ 1, 165559 ^ 1, 31684943 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18220998304703819917441 - 1) / 2 = 9110499152351909958720 from by norm_num]
      have h2 : (13 : ZMod 18220998304703819917441) ^ 9110499152351909958720 = ((18220998304703819917440 : ℕ) : ZMod 18220998304703819917441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18220998304703819917441 - 1) / 3 = 6073666101567939972480 from by norm_num]
      have h2 : (13 : ZMod 18220998304703819917441) ^ 6073666101567939972480 = ((6207593050501495652861 : ℕ) : ZMod 18220998304703819917441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18220998304703819917441 - 1) / 5 = 3644199660940763983488 from by norm_num]
      have h2 : (13 : ZMod 18220998304703819917441) ^ 3644199660940763983488 = ((871721079662526474118 : ℕ) : ZMod 18220998304703819917441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18220998304703819917441 - 1) / 23 = 792217317595818257280 from by norm_num]
      have h2 : (13 : ZMod 18220998304703819917441) ^ 792217317595818257280 = ((15088602526855018877199 : ℕ) : ZMod 18220998304703819917441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18220998304703819917441 - 1) / 157 = 116057314042699489920 from by norm_num]
      have h2 : (13 : ZMod 18220998304703819917441) ^ 116057314042699489920 = ((4553412109128438800397 : ℕ) : ZMod 18220998304703819917441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18220998304703819917441 - 1) / 167 = 109107774279663592320 from by norm_num]
      have h2 : (13 : ZMod 18220998304703819917441) ^ 109107774279663592320 = ((17627134495754611930522 : ℕ) : ZMod 18220998304703819917441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18220998304703819917441 - 1) / 165559 = 110057431518092160 from by norm_num]
      have h2 : (13 : ZMod 18220998304703819917441) ^ 110057431518092160 = ((13371645417646690773981 : ℕ) : ZMod 18220998304703819917441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18220998304703819917441 - 1) / 31684943 = 575068047454080 from by norm_num]
      have h2 : (13 : ZMod 18220998304703819917441) ^ 575068047454080 = ((16615352671947183538541 : ℕ) : ZMod 18220998304703819917441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11805572063 : Nat.Prime 11805572063 := by
  refine lucas_primality 11805572063 (5 : ZMod 11805572063) ?_ (fun q hq hd => ?_)
  · rw [show 11805572063 - 1 = 11805572062 from by norm_num]
    reduce_mod_char
  · have e : 11805572063 - 1 = [2 ^ 1, 19 ^ 1, 41 ^ 1, 7577389 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11805572063 - 1) / 2 = 5902786031 from by norm_num]
      have h2 : (5 : ZMod 11805572063) ^ 5902786031 = ((11805572062 : ℕ) : ZMod 11805572063) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11805572063 - 1) / 19 = 621345898 from by norm_num]
      have h2 : (5 : ZMod 11805572063) ^ 621345898 = ((8181134675 : ℕ) : ZMod 11805572063) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11805572063 - 1) / 41 = 287940782 from by norm_num]
      have h2 : (5 : ZMod 11805572063) ^ 287940782 = ((158604603 : ℕ) : ZMod 11805572063) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11805572063 - 1) / 7577389 = 1558 from by norm_num]
      have h2 : (5 : ZMod 11805572063) ^ 1558 = ((6124209132 : ℕ) : ZMod 11805572063) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_30977821093313 : Nat.Prime 30977821093313 := by
  refine lucas_primality 30977821093313 (3 : ZMod 30977821093313) ?_ (fun q hq hd => ?_)
  · rw [show 30977821093313 - 1 = 30977821093312 from by norm_num]
    reduce_mod_char
  · have e : 30977821093313 - 1 = [2 ^ 6, 41 ^ 1, 11805572063 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30977821093313 - 1) / 2 = 15488910546656 from by norm_num]
      have h2 : (3 : ZMod 30977821093313) ^ 15488910546656 = ((30977821093312 : ℕ) : ZMod 30977821093313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30977821093313 - 1) / 41 = 755556612032 from by norm_num]
      have h2 : (3 : ZMod 30977821093313) ^ 755556612032 = ((9627300413340 : ℕ) : ZMod 30977821093313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_11805572063).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30977821093313 - 1) / 11805572063 = 2624 from by norm_num]
      have h2 : (3 : ZMod 30977821093313) ^ 2624 = ((2277009893709 : ℕ) : ZMod 30977821093313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_408501522241 : Nat.Prime 408501522241 := by
  refine lucas_primality 408501522241 (13 : ZMod 408501522241) ?_ (fun q hq hd => ?_)
  · rw [show 408501522241 - 1 = 408501522240 from by norm_num]
    reduce_mod_char
  · have e : 408501522241 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 7 ^ 2, 8684131 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (408501522241 - 1) / 2 = 204250761120 from by norm_num]
      have h2 : (13 : ZMod 408501522241) ^ 204250761120 = ((408501522240 : ℕ) : ZMod 408501522241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (408501522241 - 1) / 3 = 136167174080 from by norm_num]
      have h2 : (13 : ZMod 408501522241) ^ 136167174080 = ((373100888756 : ℕ) : ZMod 408501522241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (408501522241 - 1) / 5 = 81700304448 from by norm_num]
      have h2 : (13 : ZMod 408501522241) ^ 81700304448 = ((127401294394 : ℕ) : ZMod 408501522241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (408501522241 - 1) / 7 = 58357360320 from by norm_num]
      have h2 : (13 : ZMod 408501522241) ^ 58357360320 = ((365818375917 : ℕ) : ZMod 408501522241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (408501522241 - 1) / 8684131 = 47040 from by norm_num]
      have h2 : (13 : ZMod 408501522241) ^ 47040 = ((80740069681 : ℕ) : ZMod 408501522241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_76642607597 : Nat.Prime 76642607597 := by
  refine lucas_primality 76642607597 (2 : ZMod 76642607597) ?_ (fun q hq hd => ?_)
  · rw [show 76642607597 - 1 = 76642607596 from by norm_num]
    reduce_mod_char
  · have e : 76642607597 - 1 = [2 ^ 2, 347 ^ 1, 4639 ^ 1, 11903 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76642607597 - 1) / 2 = 38321303798 from by norm_num]
      have h2 : (2 : ZMod 76642607597) ^ 38321303798 = ((76642607596 : ℕ) : ZMod 76642607597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76642607597 - 1) / 347 = 220872068 from by norm_num]
      have h2 : (2 : ZMod 76642607597) ^ 220872068 = ((6577909190 : ℕ) : ZMod 76642607597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76642607597 - 1) / 4639 = 16521364 from by norm_num]
      have h2 : (2 : ZMod 76642607597) ^ 16521364 = ((76228099374 : ℕ) : ZMod 76642607597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76642607597 - 1) / 11903 = 6438932 from by norm_num]
      have h2 : (2 : ZMod 76642607597) ^ 6438932 = ((69840618837 : ℕ) : ZMod 76642607597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_416472899311875644799329 : Nat.Prime 416472899311875644799329 := by
  refine lucas_primality 416472899311875644799329 (3 : ZMod 416472899311875644799329) ?_ (fun q hq hd => ?_)
  · rw [show 416472899311875644799329 - 1 = 416472899311875644799328 from by norm_num]
    reduce_mod_char
  · have e : 416472899311875644799329 - 1 = [2 ^ 5, 341323 ^ 1, 497509 ^ 1, 76642607597 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (416472899311875644799329 - 1) / 2 = 208236449655937822399664 from by norm_num]
      have h2 : (3 : ZMod 416472899311875644799329) ^ 208236449655937822399664 = ((416472899311875644799328 : ℕ) : ZMod 416472899311875644799329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (416472899311875644799329 - 1) / 341323 = 1220172386015227936 from by norm_num]
      have h2 : (3 : ZMod 416472899311875644799329) ^ 1220172386015227936 = ((67001003631681690907810 : ℕ) : ZMod 416472899311875644799329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (416472899311875644799329 - 1) / 497509 = 837116312090586592 from by norm_num]
      have h2 : (3 : ZMod 416472899311875644799329) ^ 837116312090586592 = ((130142772259796833260500 : ℕ) : ZMod 416472899311875644799329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_76642607597).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (416472899311875644799329 - 1) / 76642607597 = 5433960461024 from by norm_num]
      have h2 : (3 : ZMod 416472899311875644799329) ^ 5433960461024 = ((343887595773717375628529 : ℕ) : ZMod 416472899311875644799329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_627838273 : Nat.Prime 627838273 := by
  refine lucas_primality 627838273 (11 : ZMod 627838273) ?_ (fun q hq hd => ?_)
  · rw [show 627838273 - 1 = 627838272 from by norm_num]
    reduce_mod_char
  · have e : 627838273 - 1 = [2 ^ 6, 3 ^ 2, 947 ^ 1, 1151 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (627838273 - 1) / 2 = 313919136 from by norm_num]
      have h2 : (11 : ZMod 627838273) ^ 313919136 = ((627838272 : ℕ) : ZMod 627838273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (627838273 - 1) / 3 = 209279424 from by norm_num]
      have h2 : (11 : ZMod 627838273) ^ 209279424 = ((459269139 : ℕ) : ZMod 627838273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (627838273 - 1) / 947 = 662976 from by norm_num]
      have h2 : (11 : ZMod 627838273) ^ 662976 = ((593409298 : ℕ) : ZMod 627838273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (627838273 - 1) / 1151 = 545472 from by norm_num]
      have h2 : (11 : ZMod 627838273) ^ 545472 = ((134261175 : ℕ) : ZMod 627838273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_297545172289 : Nat.Prime 297545172289 := by
  refine lucas_primality 297545172289 (11 : ZMod 297545172289) ?_ (fun q hq hd => ?_)
  · rw [show 297545172289 - 1 = 297545172288 from by norm_num]
    reduce_mod_char
  · have e : 297545172289 - 1 = [2 ^ 6, 3 ^ 1, 7 ^ 1, 13 ^ 1, 17029829 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297545172289 - 1) / 2 = 148772586144 from by norm_num]
      have h2 : (11 : ZMod 297545172289) ^ 148772586144 = ((297545172288 : ℕ) : ZMod 297545172289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297545172289 - 1) / 3 = 99181724096 from by norm_num]
      have h2 : (11 : ZMod 297545172289) ^ 99181724096 = ((142073941840 : ℕ) : ZMod 297545172289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297545172289 - 1) / 7 = 42506453184 from by norm_num]
      have h2 : (11 : ZMod 297545172289) ^ 42506453184 = ((33110419905 : ℕ) : ZMod 297545172289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297545172289 - 1) / 13 = 22888090176 from by norm_num]
      have h2 : (11 : ZMod 297545172289) ^ 22888090176 = ((197027842762 : ℕ) : ZMod 297545172289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297545172289 - 1) / 17029829 = 17472 from by norm_num]
      have h2 : (11 : ZMod 297545172289) ^ 17472 = ((166303589178 : ℕ) : ZMod 297545172289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_56897201427233 : Nat.Prime 56897201427233 := by
  refine lucas_primality 56897201427233 (3 : ZMod 56897201427233) ?_ (fun q hq hd => ?_)
  · rw [show 56897201427233 - 1 = 56897201427232 from by norm_num]
    reduce_mod_char
  · have e : 56897201427233 - 1 = [2 ^ 5, 29 ^ 1, 37 ^ 1, 3433 ^ 1, 482689 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56897201427233 - 1) / 2 = 28448600713616 from by norm_num]
      have h2 : (3 : ZMod 56897201427233) ^ 28448600713616 = ((56897201427232 : ℕ) : ZMod 56897201427233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56897201427233 - 1) / 29 = 1961972463008 from by norm_num]
      have h2 : (3 : ZMod 56897201427233) ^ 1961972463008 = ((37088592813470 : ℕ) : ZMod 56897201427233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56897201427233 - 1) / 37 = 1537762200736 from by norm_num]
      have h2 : (3 : ZMod 56897201427233) ^ 1537762200736 = ((4798185370380 : ℕ) : ZMod 56897201427233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56897201427233 - 1) / 3433 = 16573609504 from by norm_num]
      have h2 : (3 : ZMod 56897201427233) ^ 16573609504 = ((18244478464853 : ℕ) : ZMod 56897201427233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56897201427233 - 1) / 482689 = 117875488 from by norm_num]
      have h2 : (3 : ZMod 56897201427233) ^ 117875488 = ((46565169777738 : ℕ) : ZMod 56897201427233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1533437457473 : Nat.Prime 1533437457473 := by
  refine lucas_primality 1533437457473 (3 : ZMod 1533437457473) ?_ (fun q hq hd => ?_)
  · rw [show 1533437457473 - 1 = 1533437457472 from by norm_num]
    reduce_mod_char
  · have e : 1533437457473 - 1 = [2 ^ 6, 11593 ^ 1, 2066761 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1533437457473 - 1) / 2 = 766718728736 from by norm_num]
      have h2 : (3 : ZMod 1533437457473) ^ 766718728736 = ((1533437457472 : ℕ) : ZMod 1533437457473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1533437457473 - 1) / 11593 = 132272704 from by norm_num]
      have h2 : (3 : ZMod 1533437457473) ^ 132272704 = ((53289662245 : ℕ) : ZMod 1533437457473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1533437457473 - 1) / 2066761 = 741952 from by norm_num]
      have h2 : (3 : ZMod 1533437457473) ^ 741952 = ((716972833061 : ℕ) : ZMod 1533437457473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1141723489 : Nat.Prime 1141723489 := by
  refine lucas_primality 1141723489 (19 : ZMod 1141723489) ?_ (fun q hq hd => ?_)
  · rw [show 1141723489 - 1 = 1141723488 from by norm_num]
    reduce_mod_char
  · have e : 1141723489 - 1 = [2 ^ 5, 3 ^ 1, 11892953 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1141723489 - 1) / 2 = 570861744 from by norm_num]
      have h2 : (19 : ZMod 1141723489) ^ 570861744 = ((1141723488 : ℕ) : ZMod 1141723489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1141723489 - 1) / 3 = 380574496 from by norm_num]
      have h2 : (19 : ZMod 1141723489) ^ 380574496 = ((49978610 : ℕ) : ZMod 1141723489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1141723489 - 1) / 11892953 = 96 from by norm_num]
      have h2 : (19 : ZMod 1141723489) ^ 96 = ((591401440 : ℕ) : ZMod 1141723489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_240382049 : Nat.Prime 240382049 := by
  refine lucas_primality 240382049 (3 : ZMod 240382049) ?_ (fun q hq hd => ?_)
  · rw [show 240382049 - 1 = 240382048 from by norm_num]
    reduce_mod_char
  · have e : 240382049 - 1 = [2 ^ 5, 59 ^ 1, 127321 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (240382049 - 1) / 2 = 120191024 from by norm_num]
      have h2 : (3 : ZMod 240382049) ^ 120191024 = ((240382048 : ℕ) : ZMod 240382049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (240382049 - 1) / 59 = 4074272 from by norm_num]
      have h2 : (3 : ZMod 240382049) ^ 4074272 = ((74494665 : ℕ) : ZMod 240382049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (240382049 - 1) / 127321 = 1888 from by norm_num]
      have h2 : (3 : ZMod 240382049) ^ 1888 = ((60950979 : ℕ) : ZMod 240382049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_55825839073 : Nat.Prime 55825839073 := by
  refine lucas_primality 55825839073 (5 : ZMod 55825839073) ?_ (fun q hq hd => ?_)
  · rw [show 55825839073 - 1 = 55825839072 from by norm_num]
    reduce_mod_char
  · have e : 55825839073 - 1 = [2 ^ 5, 3 ^ 2, 127 ^ 1, 1526297 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (55825839073 - 1) / 2 = 27912919536 from by norm_num]
      have h2 : (5 : ZMod 55825839073) ^ 27912919536 = ((55825839072 : ℕ) : ZMod 55825839073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (55825839073 - 1) / 3 = 18608613024 from by norm_num]
      have h2 : (5 : ZMod 55825839073) ^ 18608613024 = ((24401264624 : ℕ) : ZMod 55825839073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (55825839073 - 1) / 127 = 439573536 from by norm_num]
      have h2 : (5 : ZMod 55825839073) ^ 439573536 = ((46182002742 : ℕ) : ZMod 55825839073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (55825839073 - 1) / 1526297 = 36576 from by norm_num]
      have h2 : (5 : ZMod 55825839073) ^ 36576 = ((53766645345 : ℕ) : ZMod 55825839073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_378512609 : Nat.Prime 378512609 := by
  refine lucas_primality 378512609 (3 : ZMod 378512609) ?_ (fun q hq hd => ?_)
  · rw [show 378512609 - 1 = 378512608 from by norm_num]
    reduce_mod_char
  · have e : 378512609 - 1 = [2 ^ 5, 11828519 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (378512609 - 1) / 2 = 189256304 from by norm_num]
      have h2 : (3 : ZMod 378512609) ^ 189256304 = ((378512608 : ℕ) : ZMod 378512609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (378512609 - 1) / 11828519 = 32 from by norm_num]
      have h2 : (3 : ZMod 378512609) ^ 32 = ((356114071 : ℕ) : ZMod 378512609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_88501729 : Nat.Prime 88501729 := by
  refine lucas_primality 88501729 (11 : ZMod 88501729) ?_ (fun q hq hd => ?_)
  · rw [show 88501729 - 1 = 88501728 from by norm_num]
    reduce_mod_char
  · have e : 88501729 - 1 = [2 ^ 5, 3 ^ 1, 7 ^ 1, 17 ^ 1, 61 ^ 1, 127 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88501729 - 1) / 2 = 44250864 from by norm_num]
      have h2 : (11 : ZMod 88501729) ^ 44250864 = ((88501728 : ℕ) : ZMod 88501729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88501729 - 1) / 3 = 29500576 from by norm_num]
      have h2 : (11 : ZMod 88501729) ^ 29500576 = ((44263309 : ℕ) : ZMod 88501729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88501729 - 1) / 7 = 12643104 from by norm_num]
      have h2 : (11 : ZMod 88501729) ^ 12643104 = ((16728517 : ℕ) : ZMod 88501729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88501729 - 1) / 17 = 5205984 from by norm_num]
      have h2 : (11 : ZMod 88501729) ^ 5205984 = ((14967016 : ℕ) : ZMod 88501729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88501729 - 1) / 61 = 1450848 from by norm_num]
      have h2 : (11 : ZMod 88501729) ^ 1450848 = ((73513050 : ℕ) : ZMod 88501729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88501729 - 1) / 127 = 696864 from by norm_num]
      have h2 : (11 : ZMod 88501729) ^ 696864 = ((86744904 : ℕ) : ZMod 88501729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_140178967 : Nat.Prime 140178967 := by
  refine lucas_primality 140178967 (3 : ZMod 140178967) ?_ (fun q hq hd => ?_)
  · rw [show 140178967 - 1 = 140178966 from by norm_num]
    reduce_mod_char
  · have e : 140178967 - 1 = [2 ^ 1, 3 ^ 1, 2579 ^ 1, 9059 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (140178967 - 1) / 2 = 70089483 from by norm_num]
      have h2 : (3 : ZMod 140178967) ^ 70089483 = ((140178966 : ℕ) : ZMod 140178967) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (140178967 - 1) / 3 = 46726322 from by norm_num]
      have h2 : (3 : ZMod 140178967) ^ 46726322 = ((134309653 : ℕ) : ZMod 140178967) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (140178967 - 1) / 2579 = 54354 from by norm_num]
      have h2 : (3 : ZMod 140178967) ^ 54354 = ((27192049 : ℕ) : ZMod 140178967) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (140178967 - 1) / 9059 = 15474 from by norm_num]
      have h2 : (3 : ZMod 140178967) ^ 15474 = ((132148908 : ℕ) : ZMod 140178967) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8971453889 : Nat.Prime 8971453889 := by
  refine lucas_primality 8971453889 (3 : ZMod 8971453889) ?_ (fun q hq hd => ?_)
  · rw [show 8971453889 - 1 = 8971453888 from by norm_num]
    reduce_mod_char
  · have e : 8971453889 - 1 = [2 ^ 6, 140178967 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8971453889 - 1) / 2 = 4485726944 from by norm_num]
      have h2 : (3 : ZMod 8971453889) ^ 4485726944 = ((8971453888 : ℕ) : ZMod 8971453889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_140178967).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8971453889 - 1) / 140178967 = 64 from by norm_num]
      have h2 : (3 : ZMod 8971453889) ^ 64 = ((1230132066 : ℕ) : ZMod 8971453889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_286260692257 : Nat.Prime 286260692257 := by
  refine lucas_primality 286260692257 (5 : ZMod 286260692257) ?_ (fun q hq hd => ?_)
  · rw [show 286260692257 - 1 = 286260692256 from by norm_num]
    reduce_mod_char
  · have e : 286260692257 - 1 = [2 ^ 5, 3 ^ 2, 7 ^ 2, 11 ^ 1, 19 ^ 1, 71 ^ 1, 1367 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (286260692257 - 1) / 2 = 143130346128 from by norm_num]
      have h2 : (5 : ZMod 286260692257) ^ 143130346128 = ((286260692256 : ℕ) : ZMod 286260692257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (286260692257 - 1) / 3 = 95420230752 from by norm_num]
      have h2 : (5 : ZMod 286260692257) ^ 95420230752 = ((201941523364 : ℕ) : ZMod 286260692257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (286260692257 - 1) / 7 = 40894384608 from by norm_num]
      have h2 : (5 : ZMod 286260692257) ^ 40894384608 = ((233233501482 : ℕ) : ZMod 286260692257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (286260692257 - 1) / 11 = 26023699296 from by norm_num]
      have h2 : (5 : ZMod 286260692257) ^ 26023699296 = ((16005575392 : ℕ) : ZMod 286260692257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (286260692257 - 1) / 19 = 15066352224 from by norm_num]
      have h2 : (5 : ZMod 286260692257) ^ 15066352224 = ((276002017022 : ℕ) : ZMod 286260692257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (286260692257 - 1) / 71 = 4031840736 from by norm_num]
      have h2 : (5 : ZMod 286260692257) ^ 4031840736 = ((212640806272 : ℕ) : ZMod 286260692257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (286260692257 - 1) / 1367 = 209407968 from by norm_num]
      have h2 : (5 : ZMod 286260692257) ^ 209407968 = ((19400321036 : ℕ) : ZMod 286260692257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_896035121 : Nat.Prime 896035121 := by
  refine lucas_primality 896035121 (3 : ZMod 896035121) ?_ (fun q hq hd => ?_)
  · rw [show 896035121 - 1 = 896035120 from by norm_num]
    reduce_mod_char
  · have e : 896035121 - 1 = [2 ^ 4, 5 ^ 1, 107 ^ 1, 104677 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (896035121 - 1) / 2 = 448017560 from by norm_num]
      have h2 : (3 : ZMod 896035121) ^ 448017560 = ((896035120 : ℕ) : ZMod 896035121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (896035121 - 1) / 5 = 179207024 from by norm_num]
      have h2 : (3 : ZMod 896035121) ^ 179207024 = ((450038556 : ℕ) : ZMod 896035121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (896035121 - 1) / 107 = 8374160 from by norm_num]
      have h2 : (3 : ZMod 896035121) ^ 8374160 = ((87563144 : ℕ) : ZMod 896035121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (896035121 - 1) / 104677 = 8560 from by norm_num]
      have h2 : (3 : ZMod 896035121) ^ 8560 = ((666154859 : ℕ) : ZMod 896035121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15802442706594785921 : Nat.Prime 15802442706594785921 := by
  refine lucas_primality 15802442706594785921 (3 : ZMod 15802442706594785921) ?_ (fun q hq hd => ?_)
  · rw [show 15802442706594785921 - 1 = 15802442706594785920 from by norm_num]
    reduce_mod_char
  · have e : 15802442706594785921 - 1 = [2 ^ 7, 5 ^ 1, 7 ^ 1, 3936599 ^ 1, 896035121 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15802442706594785921 - 1) / 2 = 7901221353297392960 from by norm_num]
      have h2 : (3 : ZMod 15802442706594785921) ^ 7901221353297392960 = ((15802442706594785920 : ℕ) : ZMod 15802442706594785921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15802442706594785921 - 1) / 5 = 3160488541318957184 from by norm_num]
      have h2 : (3 : ZMod 15802442706594785921) ^ 3160488541318957184 = ((7050362848740326777 : ℕ) : ZMod 15802442706594785921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15802442706594785921 - 1) / 7 = 2257491815227826560 from by norm_num]
      have h2 : (3 : ZMod 15802442706594785921) ^ 2257491815227826560 = ((8490263618012035768 : ℕ) : ZMod 15802442706594785921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15802442706594785921 - 1) / 3936599 = 4014237342080 from by norm_num]
      have h2 : (3 : ZMod 15802442706594785921) ^ 4014237342080 = ((11056269894456091956 : ℕ) : ZMod 15802442706594785921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_896035121).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15802442706594785921 - 1) / 896035121 = 17635963520 from by norm_num]
      have h2 : (3 : ZMod 15802442706594785921) ^ 17635963520 = ((2195682755683717542 : ℕ) : ZMod 15802442706594785921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2577111937 : Nat.Prime 2577111937 := by
  refine lucas_primality 2577111937 (10 : ZMod 2577111937) ?_ (fun q hq hd => ?_)
  · rw [show 2577111937 - 1 = 2577111936 from by norm_num]
    reduce_mod_char
  · have e : 2577111937 - 1 = [2 ^ 7, 3 ^ 1, 7 ^ 1, 167 ^ 1, 5741 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2577111937 - 1) / 2 = 1288555968 from by norm_num]
      have h2 : (10 : ZMod 2577111937) ^ 1288555968 = ((2577111936 : ℕ) : ZMod 2577111937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2577111937 - 1) / 3 = 859037312 from by norm_num]
      have h2 : (10 : ZMod 2577111937) ^ 859037312 = ((1435755429 : ℕ) : ZMod 2577111937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2577111937 - 1) / 7 = 368158848 from by norm_num]
      have h2 : (10 : ZMod 2577111937) ^ 368158848 = ((2195468766 : ℕ) : ZMod 2577111937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2577111937 - 1) / 167 = 15431808 from by norm_num]
      have h2 : (10 : ZMod 2577111937) ^ 15431808 = ((1451779392 : ℕ) : ZMod 2577111937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2577111937 - 1) / 5741 = 448896 from by norm_num]
      have h2 : (10 : ZMod 2577111937) ^ 448896 = ((2001294684 : ℕ) : ZMod 2577111937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_29090486069 : Nat.Prime 29090486069 := by
  refine lucas_primality 29090486069 (2 : ZMod 29090486069) ?_ (fun q hq hd => ?_)
  · rw [show 29090486069 - 1 = 29090486068 from by norm_num]
    reduce_mod_char
  · have e : 29090486069 - 1 = [2 ^ 2, 7 ^ 1, 21407 ^ 1, 48533 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29090486069 - 1) / 2 = 14545243034 from by norm_num]
      have h2 : (2 : ZMod 29090486069) ^ 14545243034 = ((29090486068 : ℕ) : ZMod 29090486069) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29090486069 - 1) / 7 = 4155783724 from by norm_num]
      have h2 : (2 : ZMod 29090486069) ^ 4155783724 = ((1094278531 : ℕ) : ZMod 29090486069) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29090486069 - 1) / 21407 = 1358924 from by norm_num]
      have h2 : (2 : ZMod 29090486069) ^ 1358924 = ((20177335970 : ℕ) : ZMod 29090486069) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29090486069 - 1) / 48533 = 599396 from by norm_num]
      have h2 : (2 : ZMod 29090486069) ^ 599396 = ((1745512128 : ℕ) : ZMod 29090486069) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_41890299939361 : Nat.Prime 41890299939361 := by
  refine lucas_primality 41890299939361 (7 : ZMod 41890299939361) ?_ (fun q hq hd => ?_)
  · rw [show 41890299939361 - 1 = 41890299939360 from by norm_num]
    reduce_mod_char
  · have e : 41890299939361 - 1 = [2 ^ 5, 3 ^ 2, 5 ^ 1, 29090486069 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41890299939361 - 1) / 2 = 20945149969680 from by norm_num]
      have h2 : (7 : ZMod 41890299939361) ^ 20945149969680 = ((41890299939360 : ℕ) : ZMod 41890299939361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41890299939361 - 1) / 3 = 13963433313120 from by norm_num]
      have h2 : (7 : ZMod 41890299939361) ^ 13963433313120 = ((20290586094904 : ℕ) : ZMod 41890299939361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41890299939361 - 1) / 5 = 8378059987872 from by norm_num]
      have h2 : (7 : ZMod 41890299939361) ^ 8378059987872 = ((9419680280961 : ℕ) : ZMod 41890299939361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_29090486069).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41890299939361 - 1) / 29090486069 = 1440 from by norm_num]
      have h2 : (7 : ZMod 41890299939361) ^ 1440 = ((7835683086946 : ℕ) : ZMod 41890299939361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1292767882369 : Nat.Prime 1292767882369 := by
  refine lucas_primality 1292767882369 (7 : ZMod 1292767882369) ?_ (fun q hq hd => ?_)
  · rw [show 1292767882369 - 1 = 1292767882368 from by norm_num]
    reduce_mod_char
  · have e : 1292767882369 - 1 = [2 ^ 7, 3 ^ 1, 31247 ^ 1, 107741 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1292767882369 - 1) / 2 = 646383941184 from by norm_num]
      have h2 : (7 : ZMod 1292767882369) ^ 646383941184 = ((1292767882368 : ℕ) : ZMod 1292767882369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1292767882369 - 1) / 3 = 430922627456 from by norm_num]
      have h2 : (7 : ZMod 1292767882369) ^ 430922627456 = ((23298720857 : ℕ) : ZMod 1292767882369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1292767882369 - 1) / 31247 = 41372544 from by norm_num]
      have h2 : (7 : ZMod 1292767882369) ^ 41372544 = ((267983908923 : ℕ) : ZMod 1292767882369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1292767882369 - 1) / 107741 = 11998848 from by norm_num]
      have h2 : (7 : ZMod 1292767882369) ^ 11998848 = ((1063479229165 : ℕ) : ZMod 1292767882369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15910619201 : Nat.Prime 15910619201 := by
  refine lucas_primality 15910619201 (3 : ZMod 15910619201) ?_ (fun q hq hd => ?_)
  · rw [show 15910619201 - 1 = 15910619200 from by norm_num]
    reduce_mod_char
  · have e : 15910619201 - 1 = [2 ^ 6, 5 ^ 2, 7 ^ 1, 43 ^ 1, 33037 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15910619201 - 1) / 2 = 7955309600 from by norm_num]
      have h2 : (3 : ZMod 15910619201) ^ 7955309600 = ((15910619200 : ℕ) : ZMod 15910619201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15910619201 - 1) / 5 = 3182123840 from by norm_num]
      have h2 : (3 : ZMod 15910619201) ^ 3182123840 = ((7636960021 : ℕ) : ZMod 15910619201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15910619201 - 1) / 7 = 2272945600 from by norm_num]
      have h2 : (3 : ZMod 15910619201) ^ 2272945600 = ((3931010612 : ℕ) : ZMod 15910619201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15910619201 - 1) / 43 = 370014400 from by norm_num]
      have h2 : (3 : ZMod 15910619201) ^ 370014400 = ((6768625853 : ℕ) : ZMod 15910619201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15910619201 - 1) / 33037 = 481600 from by norm_num]
      have h2 : (3 : ZMod 15910619201) ^ 481600 = ((6795828520 : ℕ) : ZMod 15910619201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5818847221891037 : Nat.Prime 5818847221891037 := by
  refine lucas_primality 5818847221891037 (2 : ZMod 5818847221891037) ?_ (fun q hq hd => ?_)
  · rw [show 5818847221891037 - 1 = 5818847221891036 from by norm_num]
    reduce_mod_char
  · have e : 5818847221891037 - 1 = [2 ^ 2, 1871 ^ 1, 124951 ^ 1, 6222479 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5818847221891037 - 1) / 2 = 2909423610945518 from by norm_num]
      have h2 : (2 : ZMod 5818847221891037) ^ 2909423610945518 = ((5818847221891036 : ℕ) : ZMod 5818847221891037) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5818847221891037 - 1) / 1871 = 3110019894116 from by norm_num]
      have h2 : (2 : ZMod 5818847221891037) ^ 3110019894116 = ((3363140249913314 : ℕ) : ZMod 5818847221891037) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5818847221891037 - 1) / 124951 = 46569032836 from by norm_num]
      have h2 : (2 : ZMod 5818847221891037) ^ 46569032836 = ((3092184026001020 : ℕ) : ZMod 5818847221891037) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5818847221891037 - 1) / 6222479 = 935133284 from by norm_num]
      have h2 : (2 : ZMod 5818847221891037) ^ 935133284 = ((1844997278958155 : ℕ) : ZMod 5818847221891037) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1303421777703592289 : Nat.Prime 1303421777703592289 := by
  refine lucas_primality 1303421777703592289 (6 : ZMod 1303421777703592289) ?_ (fun q hq hd => ?_)
  · rw [show 1303421777703592289 - 1 = 1303421777703592288 from by norm_num]
    reduce_mod_char
  · have e : 1303421777703592289 - 1 = [2 ^ 5, 7 ^ 1, 5818847221891037 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1303421777703592289 - 1) / 2 = 651710888851796144 from by norm_num]
      have h2 : (6 : ZMod 1303421777703592289) ^ 651710888851796144 = ((1303421777703592288 : ℕ) : ZMod 1303421777703592289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1303421777703592289 - 1) / 7 = 186203111100513184 from by norm_num]
      have h2 : (6 : ZMod 1303421777703592289) ^ 186203111100513184 = ((935367718639798060 : ℕ) : ZMod 1303421777703592289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_5818847221891037).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1303421777703592289 - 1) / 5818847221891037 = 224 from by norm_num]
      have h2 : (6 : ZMod 1303421777703592289) ^ 224 = ((214048182678242042 : ℕ) : ZMod 1303421777703592289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3655444202623937 : Nat.Prime 3655444202623937 := by
  refine lucas_primality 3655444202623937 (3 : ZMod 3655444202623937) ?_ (fun q hq hd => ?_)
  · rw [show 3655444202623937 - 1 = 3655444202623936 from by norm_num]
    reduce_mod_char
  · have e : 3655444202623937 - 1 = [2 ^ 6, 2472329 ^ 1, 23102231 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3655444202623937 - 1) / 2 = 1827722101311968 from by norm_num]
      have h2 : (3 : ZMod 3655444202623937) ^ 1827722101311968 = ((3655444202623936 : ℕ) : ZMod 3655444202623937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3655444202623937 - 1) / 2472329 = 1478542784 from by norm_num]
      have h2 : (3 : ZMod 3655444202623937) ^ 1478542784 = ((2230004962753592 : ℕ) : ZMod 3655444202623937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3655444202623937 - 1) / 23102231 = 158229056 from by norm_num]
      have h2 : (3 : ZMod 3655444202623937) ^ 158229056 = ((3638796853710096 : ℕ) : ZMod 3655444202623937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15225314603 : Nat.Prime 15225314603 := by
  refine lucas_primality 15225314603 (2 : ZMod 15225314603) ?_ (fun q hq hd => ?_)
  · rw [show 15225314603 - 1 = 15225314602 from by norm_num]
    reduce_mod_char
  · have e : 15225314603 - 1 = [2 ^ 1, 2281 ^ 1, 3337421 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15225314603 - 1) / 2 = 7612657301 from by norm_num]
      have h2 : (2 : ZMod 15225314603) ^ 7612657301 = ((15225314602 : ℕ) : ZMod 15225314603) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15225314603 - 1) / 2281 = 6674842 from by norm_num]
      have h2 : (2 : ZMod 15225314603) ^ 6674842 = ((4371272692 : ℕ) : ZMod 15225314603) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15225314603 - 1) / 3337421 = 4562 from by norm_num]
      have h2 : (2 : ZMod 15225314603) ^ 4562 = ((4287556801 : ℕ) : ZMod 15225314603) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_273324847753057 : Nat.Prime 273324847753057 := by
  refine lucas_primality 273324847753057 (10 : ZMod 273324847753057) ?_ (fun q hq hd => ?_)
  · rw [show 273324847753057 - 1 = 273324847753056 from by norm_num]
    reduce_mod_char
  · have e : 273324847753057 - 1 = [2 ^ 5, 3 ^ 1, 11 ^ 1, 17 ^ 1, 15225314603 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (273324847753057 - 1) / 2 = 136662423876528 from by norm_num]
      have h2 : (10 : ZMod 273324847753057) ^ 136662423876528 = ((273324847753056 : ℕ) : ZMod 273324847753057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (273324847753057 - 1) / 3 = 91108282584352 from by norm_num]
      have h2 : (10 : ZMod 273324847753057) ^ 91108282584352 = ((137917008272574 : ℕ) : ZMod 273324847753057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (273324847753057 - 1) / 11 = 24847713432096 from by norm_num]
      have h2 : (10 : ZMod 273324847753057) ^ 24847713432096 = ((10455784434581 : ℕ) : ZMod 273324847753057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (273324847753057 - 1) / 17 = 16077932220768 from by norm_num]
      have h2 : (10 : ZMod 273324847753057) ^ 16077932220768 = ((48602800834373 : ℕ) : ZMod 273324847753057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_15225314603).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (273324847753057 - 1) / 15225314603 = 17952 from by norm_num]
      have h2 : (10 : ZMod 273324847753057) ^ 17952 = ((167278114189515 : ℕ) : ZMod 273324847753057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_256085953 : Nat.Prime 256085953 := by
  refine lucas_primality 256085953 (10 : ZMod 256085953) ?_ (fun q hq hd => ?_)
  · rw [show 256085953 - 1 = 256085952 from by norm_num]
    reduce_mod_char
  · have e : 256085953 - 1 = [2 ^ 6, 3 ^ 1, 19 ^ 1, 70199 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (256085953 - 1) / 2 = 128042976 from by norm_num]
      have h2 : (10 : ZMod 256085953) ^ 128042976 = ((256085952 : ℕ) : ZMod 256085953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (256085953 - 1) / 3 = 85361984 from by norm_num]
      have h2 : (10 : ZMod 256085953) ^ 85361984 = ((130140839 : ℕ) : ZMod 256085953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (256085953 - 1) / 19 = 13478208 from by norm_num]
      have h2 : (10 : ZMod 256085953) ^ 13478208 = ((38151556 : ℕ) : ZMod 256085953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (256085953 - 1) / 70199 = 3648 from by norm_num]
      have h2 : (10 : ZMod 256085953) ^ 3648 = ((212167514 : ℕ) : ZMod 256085953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_21543265124993 : Nat.Prime 21543265124993 := by
  refine lucas_primality 21543265124993 (3 : ZMod 21543265124993) ?_ (fun q hq hd => ?_)
  · rw [show 21543265124993 - 1 = 21543265124992 from by norm_num]
    reduce_mod_char
  · have e : 21543265124993 - 1 = [2 ^ 7, 13 ^ 3, 347 ^ 1, 220771 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21543265124993 - 1) / 2 = 10771632562496 from by norm_num]
      have h2 : (3 : ZMod 21543265124993) ^ 10771632562496 = ((21543265124992 : ℕ) : ZMod 21543265124993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21543265124993 - 1) / 13 = 1657174240384 from by norm_num]
      have h2 : (3 : ZMod 21543265124993) ^ 1657174240384 = ((17685594718946 : ℕ) : ZMod 21543265124993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21543265124993 - 1) / 347 = 62084337536 from by norm_num]
      have h2 : (3 : ZMod 21543265124993) ^ 62084337536 = ((15877493734597 : ℕ) : ZMod 21543265124993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21543265124993 - 1) / 220771 = 97581952 from by norm_num]
      have h2 : (3 : ZMod 21543265124993) ^ 97581952 = ((18722538582785 : ℕ) : ZMod 21543265124993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_34880117533 : Nat.Prime 34880117533 := by
  refine lucas_primality 34880117533 (11 : ZMod 34880117533) ?_ (fun q hq hd => ?_)
  · rw [show 34880117533 - 1 = 34880117532 from by norm_num]
    reduce_mod_char
  · have e : 34880117533 - 1 = [2 ^ 2, 3 ^ 1, 13 ^ 2, 43 ^ 1, 399983 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34880117533 - 1) / 2 = 17440058766 from by norm_num]
      have h2 : (11 : ZMod 34880117533) ^ 17440058766 = ((34880117532 : ℕ) : ZMod 34880117533) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34880117533 - 1) / 3 = 11626705844 from by norm_num]
      have h2 : (11 : ZMod 34880117533) ^ 11626705844 = ((17704072397 : ℕ) : ZMod 34880117533) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34880117533 - 1) / 13 = 2683085964 from by norm_num]
      have h2 : (11 : ZMod 34880117533) ^ 2683085964 = ((16012307141 : ℕ) : ZMod 34880117533) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34880117533 - 1) / 43 = 811165524 from by norm_num]
      have h2 : (11 : ZMod 34880117533) ^ 811165524 = ((11625227572 : ℕ) : ZMod 34880117533) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34880117533 - 1) / 399983 = 87204 from by norm_num]
      have h2 : (11 : ZMod 34880117533) ^ 87204 = ((32132369889 : ℕ) : ZMod 34880117533) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_298058138424872129 : Nat.Prime 298058138424872129 := by
  refine lucas_primality 298058138424872129 (3 : ZMod 298058138424872129) ?_ (fun q hq hd => ?_)
  · rw [show 298058138424872129 - 1 = 298058138424872128 from by norm_num]
    reduce_mod_char
  · have e : 298058138424872129 - 1 = [2 ^ 6, 133519 ^ 1, 34880117533 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (298058138424872129 - 1) / 2 = 149029069212436064 from by norm_num]
      have h2 : (3 : ZMod 298058138424872129) ^ 149029069212436064 = ((298058138424872128 : ℕ) : ZMod 298058138424872129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (298058138424872129 - 1) / 133519 = 2232327522112 from by norm_num]
      have h2 : (3 : ZMod 298058138424872129) ^ 2232327522112 = ((283463595511414018 : ℕ) : ZMod 298058138424872129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_34880117533).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (298058138424872129 - 1) / 34880117533 = 8545216 from by norm_num]
      have h2 : (3 : ZMod 298058138424872129) ^ 8545216 = ((157876978065278321 : ℕ) : ZMod 298058138424872129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1793194545851 : Nat.Prime 1793194545851 := by
  refine lucas_primality 1793194545851 (7 : ZMod 1793194545851) ?_ (fun q hq hd => ?_)
  · rw [show 1793194545851 - 1 = 1793194545850 from by norm_num]
    reduce_mod_char
  · have e : 1793194545851 - 1 = [2 ^ 1, 5 ^ 2, 31 ^ 1, 193 ^ 1, 211 ^ 1, 28409 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1793194545851 - 1) / 2 = 896597272925 from by norm_num]
      have h2 : (7 : ZMod 1793194545851) ^ 896597272925 = ((1793194545850 : ℕ) : ZMod 1793194545851) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1793194545851 - 1) / 5 = 358638909170 from by norm_num]
      have h2 : (7 : ZMod 1793194545851) ^ 358638909170 = ((386219027212 : ℕ) : ZMod 1793194545851) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1793194545851 - 1) / 31 = 57844985350 from by norm_num]
      have h2 : (7 : ZMod 1793194545851) ^ 57844985350 = ((341414109435 : ℕ) : ZMod 1793194545851) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1793194545851 - 1) / 193 = 9291163450 from by norm_num]
      have h2 : (7 : ZMod 1793194545851) ^ 9291163450 = ((1714810480375 : ℕ) : ZMod 1793194545851) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1793194545851 - 1) / 211 = 8498552350 from by norm_num]
      have h2 : (7 : ZMod 1793194545851) ^ 8498552350 = ((1616163647634 : ℕ) : ZMod 1793194545851) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1793194545851 - 1) / 28409 = 63120650 from by norm_num]
      have h2 : (7 : ZMod 1793194545851) ^ 63120650 = ((156743324498 : ℕ) : ZMod 1793194545851) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_57382225467233 : Nat.Prime 57382225467233 := by
  refine lucas_primality 57382225467233 (3 : ZMod 57382225467233) ?_ (fun q hq hd => ?_)
  · rw [show 57382225467233 - 1 = 57382225467232 from by norm_num]
    reduce_mod_char
  · have e : 57382225467233 - 1 = [2 ^ 5, 1793194545851 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57382225467233 - 1) / 2 = 28691112733616 from by norm_num]
      have h2 : (3 : ZMod 57382225467233) ^ 28691112733616 = ((57382225467232 : ℕ) : ZMod 57382225467233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1793194545851).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57382225467233 - 1) / 1793194545851 = 32 from by norm_num]
      have h2 : (3 : ZMod 57382225467233) ^ 32 = ((16788973900385 : ℕ) : ZMod 57382225467233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1131373313990260993 : Nat.Prime 1131373313990260993 := by
  refine lucas_primality 1131373313990260993 (5 : ZMod 1131373313990260993) ?_ (fun q hq hd => ?_)
  · rw [show 1131373313990260993 - 1 = 1131373313990260992 from by norm_num]
    reduce_mod_char
  · have e : 1131373313990260993 - 1 = [2 ^ 8, 3 ^ 2, 7 ^ 1, 5911201 ^ 1, 11867239 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1131373313990260993 - 1) / 2 = 565686656995130496 from by norm_num]
      have h2 : (5 : ZMod 1131373313990260993) ^ 565686656995130496 = ((1131373313990260992 : ℕ) : ZMod 1131373313990260993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1131373313990260993 - 1) / 3 = 377124437996753664 from by norm_num]
      have h2 : (5 : ZMod 1131373313990260993) ^ 377124437996753664 = ((752949430040449636 : ℕ) : ZMod 1131373313990260993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1131373313990260993 - 1) / 7 = 161624759141465856 from by norm_num]
      have h2 : (5 : ZMod 1131373313990260993) ^ 161624759141465856 = ((1093441703670590977 : ℕ) : ZMod 1131373313990260993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1131373313990260993 - 1) / 5911201 = 191394830592 from by norm_num]
      have h2 : (5 : ZMod 1131373313990260993) ^ 191394830592 = ((389591936509240333 : ℕ) : ZMod 1131373313990260993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1131373313990260993 - 1) / 11867239 = 95335849728 from by norm_num]
      have h2 : (5 : ZMod 1131373313990260993) ^ 95335849728 = ((1057917287817727405 : ℕ) : ZMod 1131373313990260993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_724078920953767035521 : Nat.Prime 724078920953767035521 := by
  refine lucas_primality 724078920953767035521 (11 : ZMod 724078920953767035521) ?_ (fun q hq hd => ?_)
  · rw [show 724078920953767035521 - 1 = 724078920953767035520 from by norm_num]
    reduce_mod_char
  · have e : 724078920953767035521 - 1 = [2 ^ 7, 5 ^ 1, 1131373313990260993 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (724078920953767035521 - 1) / 2 = 362039460476883517760 from by norm_num]
      have h2 : (11 : ZMod 724078920953767035521) ^ 362039460476883517760 = ((724078920953767035520 : ℕ) : ZMod 724078920953767035521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (724078920953767035521 - 1) / 5 = 144815784190753407104 from by norm_num]
      have h2 : (11 : ZMod 724078920953767035521) ^ 144815784190753407104 = ((476007712563609113026 : ℕ) : ZMod 724078920953767035521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1131373313990260993).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (724078920953767035521 - 1) / 1131373313990260993 = 640 from by norm_num]
      have h2 : (11 : ZMod 724078920953767035521) ^ 640 = ((329338183567751482508 : ℕ) : ZMod 724078920953767035521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_14003094817 : Nat.Prime 14003094817 := by
  refine lucas_primality 14003094817 (5 : ZMod 14003094817) ?_ (fun q hq hd => ?_)
  · rw [show 14003094817 - 1 = 14003094816 from by norm_num]
    reduce_mod_char
  · have e : 14003094817 - 1 = [2 ^ 5, 3 ^ 2, 31 ^ 1, 89 ^ 1, 17623 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14003094817 - 1) / 2 = 7001547408 from by norm_num]
      have h2 : (5 : ZMod 14003094817) ^ 7001547408 = ((14003094816 : ℕ) : ZMod 14003094817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14003094817 - 1) / 3 = 4667698272 from by norm_num]
      have h2 : (5 : ZMod 14003094817) ^ 4667698272 = ((7254048888 : ℕ) : ZMod 14003094817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14003094817 - 1) / 31 = 451712736 from by norm_num]
      have h2 : (5 : ZMod 14003094817) ^ 451712736 = ((3555143841 : ℕ) : ZMod 14003094817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14003094817 - 1) / 89 = 157338144 from by norm_num]
      have h2 : (5 : ZMod 14003094817) ^ 157338144 = ((6999239622 : ℕ) : ZMod 14003094817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14003094817 - 1) / 17623 = 794592 from by norm_num]
      have h2 : (5 : ZMod 14003094817) ^ 794592 = ((1406057792 : ℕ) : ZMod 14003094817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3481187233 : Nat.Prime 3481187233 := by
  refine lucas_primality 3481187233 (7 : ZMod 3481187233) ?_ (fun q hq hd => ?_)
  · rw [show 3481187233 - 1 = 3481187232 from by norm_num]
    reduce_mod_char
  · have e : 3481187233 - 1 = [2 ^ 5, 3 ^ 1, 1693 ^ 1, 21419 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3481187233 - 1) / 2 = 1740593616 from by norm_num]
      have h2 : (7 : ZMod 3481187233) ^ 1740593616 = ((3481187232 : ℕ) : ZMod 3481187233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3481187233 - 1) / 3 = 1160395744 from by norm_num]
      have h2 : (7 : ZMod 3481187233) ^ 1160395744 = ((1210112372 : ℕ) : ZMod 3481187233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3481187233 - 1) / 1693 = 2056224 from by norm_num]
      have h2 : (7 : ZMod 3481187233) ^ 2056224 = ((1074108408 : ℕ) : ZMod 3481187233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3481187233 - 1) / 21419 = 162528 from by norm_num]
      have h2 : (7 : ZMod 3481187233) ^ 162528 = ((2856163828 : ℕ) : ZMod 3481187233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3475883681 : Nat.Prime 3475883681 := by
  refine lucas_primality 3475883681 (3 : ZMod 3475883681) ?_ (fun q hq hd => ?_)
  · rw [show 3475883681 - 1 = 3475883680 from by norm_num]
    reduce_mod_char
  · have e : 3475883681 - 1 = [2 ^ 5, 5 ^ 1, 31 ^ 1, 193 ^ 1, 3631 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3475883681 - 1) / 2 = 1737941840 from by norm_num]
      have h2 : (3 : ZMod 3475883681) ^ 1737941840 = ((3475883680 : ℕ) : ZMod 3475883681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3475883681 - 1) / 5 = 695176736 from by norm_num]
      have h2 : (3 : ZMod 3475883681) ^ 695176736 = ((2813073461 : ℕ) : ZMod 3475883681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3475883681 - 1) / 31 = 112125280 from by norm_num]
      have h2 : (3 : ZMod 3475883681) ^ 112125280 = ((2488279848 : ℕ) : ZMod 3475883681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3475883681 - 1) / 193 = 18009760 from by norm_num]
      have h2 : (3 : ZMod 3475883681) ^ 18009760 = ((667975690 : ℕ) : ZMod 3475883681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3475883681 - 1) / 3631 = 957280 from by norm_num]
      have h2 : (3 : ZMod 3475883681) ^ 957280 = ((1613836634 : ℕ) : ZMod 3475883681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_44585571617 : Nat.Prime 44585571617 := by
  refine lucas_primality 44585571617 (3 : ZMod 44585571617) ?_ (fun q hq hd => ?_)
  · rw [show 44585571617 - 1 = 44585571616 from by norm_num]
    reduce_mod_char
  · have e : 44585571617 - 1 = [2 ^ 5, 29 ^ 1, 673 ^ 1, 71389 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44585571617 - 1) / 2 = 22292785808 from by norm_num]
      have h2 : (3 : ZMod 44585571617) ^ 22292785808 = ((44585571616 : ℕ) : ZMod 44585571617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44585571617 - 1) / 29 = 1537433504 from by norm_num]
      have h2 : (3 : ZMod 44585571617) ^ 1537433504 = ((9050131695 : ℕ) : ZMod 44585571617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44585571617 - 1) / 673 = 66248992 from by norm_num]
      have h2 : (3 : ZMod 44585571617) ^ 66248992 = ((14054107154 : ℕ) : ZMod 44585571617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44585571617 - 1) / 71389 = 624544 from by norm_num]
      have h2 : (3 : ZMod 44585571617) ^ 624544 = ((22509088539 : ℕ) : ZMod 44585571617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5542095809 : Nat.Prime 5542095809 := by
  refine lucas_primality 5542095809 (3 : ZMod 5542095809) ?_ (fun q hq hd => ?_)
  · rw [show 5542095809 - 1 = 5542095808 from by norm_num]
    reduce_mod_char
  · have e : 5542095809 - 1 = [2 ^ 6, 29 ^ 2, 102967 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5542095809 - 1) / 2 = 2771047904 from by norm_num]
      have h2 : (3 : ZMod 5542095809) ^ 2771047904 = ((5542095808 : ℕ) : ZMod 5542095809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5542095809 - 1) / 29 = 191106752 from by norm_num]
      have h2 : (3 : ZMod 5542095809) ^ 191106752 = ((843393065 : ℕ) : ZMod 5542095809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5542095809 - 1) / 102967 = 53824 from by norm_num]
      have h2 : (3 : ZMod 5542095809) ^ 53824 = ((2403032756 : ℕ) : ZMod 5542095809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_336291223 : Nat.Prime 336291223 := by
  refine lucas_primality 336291223 (5 : ZMod 336291223) ?_ (fun q hq hd => ?_)
  · rw [show 336291223 - 1 = 336291222 from by norm_num]
    reduce_mod_char
  · have e : 336291223 - 1 = [2 ^ 1, 3 ^ 1, 19 ^ 1, 2949923 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (336291223 - 1) / 2 = 168145611 from by norm_num]
      have h2 : (5 : ZMod 336291223) ^ 168145611 = ((336291222 : ℕ) : ZMod 336291223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (336291223 - 1) / 3 = 112097074 from by norm_num]
      have h2 : (5 : ZMod 336291223) ^ 112097074 = ((168006857 : ℕ) : ZMod 336291223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (336291223 - 1) / 19 = 17699538 from by norm_num]
      have h2 : (5 : ZMod 336291223) ^ 17699538 = ((52036236 : ℕ) : ZMod 336291223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (336291223 - 1) / 2949923 = 114 from by norm_num]
      have h2 : (5 : ZMod 336291223) ^ 114 = ((107756206 : ℕ) : ZMod 336291223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_36853030570720289 : Nat.Prime 36853030570720289 := by
  refine lucas_primality 36853030570720289 (3 : ZMod 36853030570720289) ?_ (fun q hq hd => ?_)
  · rw [show 36853030570720289 - 1 = 36853030570720288 from by norm_num]
    reduce_mod_char
  · have e : 36853030570720289 - 1 = [2 ^ 5, 283 ^ 1, 12101 ^ 1, 336291223 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (36853030570720289 - 1) / 2 = 18426515285360144 from by norm_num]
      have h2 : (3 : ZMod 36853030570720289) ^ 18426515285360144 = ((36853030570720288 : ℕ) : ZMod 36853030570720289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (36853030570720289 - 1) / 283 = 130222722864736 from by norm_num]
      have h2 : (3 : ZMod 36853030570720289) ^ 130222722864736 = ((10576304434933436 : ℕ) : ZMod 36853030570720289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (36853030570720289 - 1) / 12101 = 3045453315488 from by norm_num]
      have h2 : (3 : ZMod 36853030570720289) ^ 3045453315488 = ((3161407110323228 : ℕ) : ZMod 36853030570720289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_336291223).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (36853030570720289 - 1) / 336291223 = 109586656 from by norm_num]
      have h2 : (3 : ZMod 36853030570720289) ^ 109586656 = ((27982161000033552 : ℕ) : ZMod 36853030570720289) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

set_option maxHeartbeats 12000000 in
theorem zs_0 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 7 ≤ z) (hi : z < 300)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 = 8 → z ∈ ({7} : Finset ℕ)) ∧
    (e % 32 = 16 → z ∈ ({7, 41, 73, 113, 157, 167, 173, 199, 307, 449, 599, 607, 617, 643, 743, 811, 937, 967, 1201,
      1213, 1237, 1249, 1277, 1297, 1373, 1579, 1637, 1667, 1747, 1979, 2011, 2027} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 7
    · simp
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 11
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 11 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g51329 := S7 51329 (by norm_num) (by norm_num) (by decide) ((by norm_num : 51329 ∣ 1 + 11 ^ 16).trans hd)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 51329 g51329 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 51329 g51329 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 13
    · exfalso; have hd := D8 he
      have g407865361 := S7 407865361 prime_407865361 (by norm_num) (by decide) ((by norm_num : 407865361 ∣ 1 + 13 ^ 8).trans hd)
      have g12583 := S1 12583 (by norm_num) (by norm_num) (by decide) 407865361 g407865361 (by norm_num)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 12583 g12583 (by norm_num)
    · exfalso; have hd := D16 he
      have g441281 := S7 441281 (by norm_num) (by norm_num) (by decide) ((by norm_num : 441281 ∣ 1 + 13 ^ 16).trans hd)
      have g73547 := S1 73547 (by norm_num) (by norm_num) (by decide) 441281 g441281 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 73547 g73547 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 17
    · exfalso; have hd := D8 he
      have g18913 := S7 18913 (by norm_num) (by norm_num) (by decide) ((by norm_num : 18913 ∣ 1 + 17 ^ 8).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 18913 g18913 (by norm_num)
    · exfalso; have hd := D16 he
      have g1801601 := S7 1801601 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1801601 ∣ 1 + 17 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1801601 g1801601 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 19
    · exfalso; have hd := D8 he
      have g563377 := S7 563377 (by norm_num) (by norm_num) (by decide) ((by norm_num : 563377 ∣ 1 + 19 ^ 8).trans hd)
      have g2789 := S1 2789 (by norm_num) (by norm_num) (by decide) 563377 g563377 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2789 g2789 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 19 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 23
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 23 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 23 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 29
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 29 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g125123236840173674393761 := S7 125123236840173674393761 prime_125123236840173674393761 (by norm_num) (by decide) ((by norm_num : 125123236840173674393761 ∣ 1 + 29 ^ 16).trans hd)
      have g95617 := S1 95617 (by norm_num) (by norm_num) (by decide) 125123236840173674393761 g125123236840173674393761 (by norm_num)
      have g47809 := S1 47809 (by norm_num) (by norm_num) (by decide) 95617 g95617 (by norm_num)
      have g683 := S1 683 (by norm_num) (by norm_num) (by decide) 47809 g47809 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 683 g683 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 31
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 31 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g6139297 := S7 6139297 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6139297 ∣ 1 + 31 ^ 16).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 6139297 g6139297 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 37
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 37 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g5566657 := S7 5566657 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5566657 ∣ 1 + 37 ^ 16).trans hd)
      have g557 := S1 557 (by norm_num) (by norm_num) (by decide) 5566657 g5566657 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 557 g557 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 41
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 41 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 43
    · exfalso; have hd := D8 he
      have g5844100138801 := S7 5844100138801 prime_5844100138801 (by norm_num) (by decide) ((by norm_num : 5844100138801 ∣ 1 + 43 ^ 8).trans hd)
      have g67 := S1 67 (by norm_num) (by norm_num) (by decide) 5844100138801 g5844100138801 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g769 := S7 769 (by norm_num) (by norm_num) (by decide) ((by norm_num : 769 ∣ 1 + 43 ^ 16).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 769 g769 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 769 g769 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 47
    · exfalso; have hd := D8 he
      have g11905643330881 := S7 11905643330881 prime_11905643330881 (by norm_num) (by decide) ((by norm_num : 11905643330881 ∣ 1 + 47 ^ 8).trans hd)
      have g850403095063 := S1 850403095063 prime_850403095063 (by norm_num) (by decide) 11905643330881 g11905643330881 (by norm_num)
      have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 850403095063 g850403095063 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 11905643330881 g11905643330881 41 g41 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g5441 := S7 5441 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5441 ∣ 1 + 47 ^ 16).trans hd)
      have g907 := S1 907 (by norm_num) (by norm_num) (by decide) 5441 g5441 (by norm_num)
      have g227 := S1 227 (by norm_num) (by norm_num) (by decide) 907 g907 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5441 g5441 227 g227 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 53
    · exfalso; have hd := D8 he
      have g31129845205681 := S7 31129845205681 prime_31129845205681 (by norm_num) (by decide) ((by norm_num : 31129845205681 ∣ 1 + 53 ^ 8).trans hd)
      have g5743 := S1 5743 (by norm_num) (by norm_num) (by decide) 31129845205681 g31129845205681 (by norm_num)
      have g359 := S1 359 (by norm_num) (by norm_num) (by decide) 5743 g5743 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 359 g359 (by norm_num)
    · exfalso; have hd := D16 he
      have g136593761 := S7 136593761 prime_136593761 (by norm_num) (by decide) ((by norm_num : 136593761 ∣ 1 + 53 ^ 16).trans hd)
      have g373207 := S1 373207 (by norm_num) (by norm_num) (by decide) 136593761 g136593761 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 373207 g373207 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 136593761 g136593761 11 g11 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 59
    · exfalso; have hd := D8 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 59 ^ 8).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · exfalso; have hd := D16 he
      have g1336981409 := S7 1336981409 prime_1336981409 (by norm_num) (by decide) ((by norm_num : 1336981409 ∣ 1 + 59 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1336981409 g1336981409 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 61
    · exfalso; have hd := D8 he
      have g12401 := S7 12401 (by norm_num) (by norm_num) (by decide) ((by norm_num : 12401 ∣ 1 + 61 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 12401 g12401 (by norm_num)
    · exfalso; have hd := D16 he
      have g13483201 := S7 13483201 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13483201 ∣ 1 + 61 ^ 16).trans hd)
      have g7499 := S1 7499 (by norm_num) (by norm_num) (by decide) 13483201 g13483201 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 7499 g7499 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 67
    · exfalso; have hd := D8 he
      have g28097 := S7 28097 (by norm_num) (by norm_num) (by decide) ((by norm_num : 28097 ∣ 1 + 67 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 28097 g28097 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 67 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 71
    · exfalso; have hd := D8 he
      have g577 := S7 577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 577 ∣ 1 + 71 ^ 8).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
    · exfalso; have hd := D16 he
      have g190404353 := S7 190404353 prime_190404353 (by norm_num) (by decide) ((by norm_num : 190404353 ∣ 1 + 71 ^ 16).trans hd)
      have g4493 := S1 4493 (by norm_num) (by norm_num) (by decide) 190404353 g190404353 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 190404353 g190404353 4493 g4493 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 73
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 73 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 79
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 79 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1021793 := S7 1021793 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1021793 ∣ 1 + 79 ^ 16).trans hd)
      have g170299 := S1 170299 (by norm_num) (by norm_num) (by decide) 1021793 g1021793 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 170299 g170299 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 83
    · exfalso; have hd := D8 he
      have g16001 := S7 16001 (by norm_num) (by norm_num) (by decide) ((by norm_num : 16001 ∣ 1 + 83 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 16001 g16001 (by norm_num)
    · exfalso; have hd := D16 he
      have g80486459297 := S7 80486459297 prime_80486459297 (by norm_num) (by decide) ((by norm_num : 80486459297 ∣ 1 + 83 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 80486459297 g80486459297 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 89
    · exfalso; have hd := D8 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 89 ^ 8).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g20922017 := S7 20922017 (by norm_num) (by norm_num) (by decide) ((by norm_num : 20922017 ∣ 1 + 89 ^ 16).trans hd)
      have g773 := S1 773 (by norm_num) (by norm_num) (by decide) 20922017 g20922017 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 773 g773 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 97
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 97 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g7681 := S7 7681 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7681 ∣ 1 + 97 ^ 16).trans hd)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 7681 g7681 (by norm_num)
      have g167 := S1 167 (by norm_num) (by norm_num) (by decide) 7681 g7681 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 23 g23 167 g167 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 101
    · exfalso; have hd := D8 he
      have g929 := S7 929 (by norm_num) (by norm_num) (by decide) ((by norm_num : 929 ∣ 1 + 101 ^ 8).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 929 g929 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 929 g929 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := S7 353 (by norm_num) (by norm_num) (by decide) ((by norm_num : 353 ∣ 1 + 101 ^ 16).trans hd)
      have g1822529 := S7 1822529 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1822529 ∣ 1 + 101 ^ 16).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 353 g353 1822529 g1822529 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 103
    · exfalso; have hd := D8 he
      have g10433 := S7 10433 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10433 ∣ 1 + 103 ^ 8).trans hd)
      have g47 := S1 47 (by norm_num) (by norm_num) (by decide) 10433 g10433 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 10433 g10433 47 g47 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g118369 := S7 118369 (by norm_num) (by norm_num) (by decide) ((by norm_num : 118369 ∣ 1 + 103 ^ 16).trans hd)
      have g89 := S1 89 (by norm_num) (by norm_num) (by decide) 118369 g118369 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 107
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 107 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g673 := S7 673 (by norm_num) (by norm_num) (by decide) ((by norm_num : 673 ∣ 1 + 107 ^ 16).trans hd)
      have g337 := S1 337 (by norm_num) (by norm_num) (by decide) 673 g673 (by norm_num)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 109
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 109 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1601 := S7 1601 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1601 ∣ 1 + 109 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1601 g1601 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 113
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 113 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 127
    · exfalso; have hd := D8 he
      have g14369 := S7 14369 (by norm_num) (by norm_num) (by decide) ((by norm_num : 14369 ∣ 1 + 127 ^ 8).trans hd)
      have g479 := S1 479 (by norm_num) (by norm_num) (by decide) 14369 g14369 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 14369 g14369 479 g479 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g577 := S7 577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 577 ∣ 1 + 127 ^ 16).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 131
    · exfalso; have hd := D8 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 131 ^ 8).trans hd)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 131 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 137
    · exfalso; have hd := D8 he
      have g1095793 := S7 1095793 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1095793 ∣ 1 + 137 ^ 8).trans hd)
      have g2699 := S1 2699 (by norm_num) (by norm_num) (by decide) 1095793 g1095793 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2699 g2699 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := S7 257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 257 ∣ 1 + 137 ^ 16).trans hd)
      have g353 := S7 353 (by norm_num) (by norm_num) (by decide) ((by norm_num : 353 ∣ 1 + 137 ^ 16).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 257 g257 353 g353 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 139
    · exfalso; have hd := D8 he
      have g77681 := S7 77681 (by norm_num) (by norm_num) (by decide) ((by norm_num : 77681 ∣ 1 + 139 ^ 8).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 77681 g77681 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 139 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 149
    · exfalso; have hd := D8 he
      have g23873 := S7 23873 (by norm_num) (by norm_num) (by decide) ((by norm_num : 23873 ∣ 1 + 149 ^ 8).trans hd)
      have g173 := S1 173 (by norm_num) (by norm_num) (by decide) 23873 g23873 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 23873 g23873 173 g173 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 149 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 151
    · exfalso; have hd := D8 he
      have g74561 := S7 74561 (by norm_num) (by norm_num) (by decide) ((by norm_num : 74561 ∣ 1 + 151 ^ 8).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 74561 g74561 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 151 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 157
    · exfalso; have hd := D8 he
      have g1297 := S7 1297 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1297 ∣ 1 + 157 ^ 8).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 1297 g1297 (by norm_num)
      have g59 := S1 59 (by norm_num) (by norm_num) (by decide) 1297 g1297 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 11 g11 59 g59 (by norm_num) (by norm_num)) (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 163
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 163 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g577 := S7 577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 577 ∣ 1 + 163 ^ 16).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 167
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 167 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 173
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 173 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 179
    · exfalso; have hd := D8 he
      have g1009 := S7 1009 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1009 ∣ 1 + 179 ^ 8).trans hd)
      have g101 := S1 101 (by norm_num) (by norm_num) (by decide) 1009 g1009 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 101 g101 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 179 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 181
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 181 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g6113 := S7 6113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6113 ∣ 1 + 181 ^ 16).trans hd)
      have g1019 := S1 1019 (by norm_num) (by norm_num) (by decide) 6113 g6113 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 6113 g6113 1019 g1019 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 191
    · exfalso; have hd := D8 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 191 ^ 8).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · exfalso; have hd := D16 he
      have g25537 := S7 25537 (by norm_num) (by norm_num) (by decide) ((by norm_num : 25537 ∣ 1 + 191 ^ 16).trans hd)
      exact S6 113 (by norm_num) (by norm_num) (by decide) 25537 g25537 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 193
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 193 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g3329 := S7 3329 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3329 ∣ 1 + 193 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 3329 g3329 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 197
    · exfalso; have hd := D8 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 197 ^ 8).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := S7 257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 257 ∣ 1 + 197 ^ 16).trans hd)
      have g929 := S7 929 (by norm_num) (by norm_num) (by decide) ((by norm_num : 929 ∣ 1 + 197 ^ 16).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 257 g257 929 g929 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 199
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 199 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 211
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 211 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g18220998304703819917441 := S7 18220998304703819917441 prime_18220998304703819917441 (by norm_num) (by decide) ((by norm_num : 18220998304703819917441 ∣ 1 + 211 ^ 16).trans hd)
      have g262331 := S1 262331 (by norm_num) (by norm_num) (by decide) 18220998304703819917441 g18220998304703819917441 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 262331 g262331 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 223
    · exfalso; have hd := D8 he
      have g618577 := S7 618577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 618577 ∣ 1 + 223 ^ 8).trans hd)
      have g309289 := S1 309289 (by norm_num) (by norm_num) (by decide) 618577 g618577 (by norm_num)
      have g197 := S1 197 (by norm_num) (by norm_num) (by decide) 309289 g309289 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 197 g197 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := S7 257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 257 ∣ 1 + 223 ^ 16).trans hd)
      have g43 := S1 43 (by norm_num) (by norm_num) (by decide) 257 g257 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 43 g43 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 257 g257 11 g11 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 227
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 227 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g4801 := S7 4801 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4801 ∣ 1 + 227 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 4801 g4801 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 229
    · exfalso; have hd := D8 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 229 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
    · exfalso; have hd := D16 he
      have g53569 := S7 53569 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53569 ∣ 1 + 229 ^ 16).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 53569 g53569 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 53569 g53569 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 233
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 233 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g3169 := S7 3169 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3169 ∣ 1 + 233 ^ 16).trans hd)
      have g317 := S1 317 (by norm_num) (by norm_num) (by decide) 3169 g3169 (by norm_num)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 317 g317 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 239
    · exfalso; have hd := D8 he
      have g5322960113892133441 := S7 5322960113892133441 prime_5322960113892133441 (by norm_num) (by decide) ((by norm_num : 5322960113892133441 ∣ 1 + 239 ^ 8).trans hd)
      have g3515089 := S1 3515089 (by norm_num) (by norm_num) (by decide) 5322960113892133441 g5322960113892133441 (by norm_num)
      exact absurd (S3 31 (by norm_num) (by norm_num) (by decide) 5322960113892133441 g5322960113892133441 3515089 g3515089 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g346337 := S7 346337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 346337 ∣ 1 + 239 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 346337 g346337 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 241
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 241 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1889 := S7 1889 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1889 ∣ 1 + 241 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1889 g1889 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 251
    · exfalso; have hd := D8 he
      have g14517809 := S7 14517809 (by norm_num) (by norm_num) (by decide) ((by norm_num : 14517809 ∣ 1 + 251 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 14517809 g14517809 (by norm_num)
    · exfalso; have hd := D16 he
      have g344801 := S7 344801 (by norm_num) (by norm_num) (by decide) ((by norm_num : 344801 ∣ 1 + 251 ^ 16).trans hd)
      have g57467 := S1 57467 (by norm_num) (by norm_num) (by decide) 344801 g344801 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 344801 g344801 57467 g57467 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 257
    · exfalso; have hd := D8 he
      have g1601 := S7 1601 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1601 ∣ 1 + 257 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1601 g1601 (by norm_num)
    · exfalso; have hd := D16 he
      have g25409 := S7 25409 (by norm_num) (by norm_num) (by decide) ((by norm_num : 25409 ∣ 1 + 257 ^ 16).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 25409 g25409 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 263
    · exfalso; have hd := D8 he
      have g2859137 := S7 2859137 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2859137 ∣ 1 + 263 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2859137 g2859137 (by norm_num)
    · exfalso; have hd := D16 he
      have g577 := S7 577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 577 ∣ 1 + 263 ^ 16).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 269
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 269 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g929 := S7 929 (by norm_num) (by norm_num) (by decide) ((by norm_num : 929 ∣ 1 + 269 ^ 16).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 929 g929 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 929 g929 5 g5 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 271
    · exfalso; have hd := D8 he
      have g2822593 := S7 2822593 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2822593 ∣ 1 + 271 ^ 8).trans hd)
      have g1411297 := S1 1411297 (by norm_num) (by norm_num) (by decide) 2822593 g2822593 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 1411297 g1411297 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 271 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 277
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 277 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g4673 := S7 4673 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4673 ∣ 1 + 277 ^ 16).trans hd)
      have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 4673 g4673 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 4673 g4673 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 281
    · exfalso; have hd := D8 he
      have g340577 := S7 340577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 340577 ∣ 1 + 281 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 340577 g340577 (by norm_num)
    · exfalso; have hd := D16 he
      have g3457 := S7 3457 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3457 ∣ 1 + 281 ^ 16).trans hd)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 3457 g3457 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 3457 g3457 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 283
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 283 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1697 := S7 1697 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1697 ∣ 1 + 283 ^ 16).trans hd)
      have g120929 := S7 120929 (by norm_num) (by norm_num) (by decide) ((by norm_num : 120929 ∣ 1 + 283 ^ 16).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1697 g1697 120929 g120929 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 293
    · exfalso; have hd := D8 he
      have g353 := S7 353 (by norm_num) (by norm_num) (by decide) ((by norm_num : 353 ∣ 1 + 293 ^ 8).trans hd)
      have g59 := S1 59 (by norm_num) (by norm_num) (by decide) 353 g353 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 353 g353 59 g59 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g1409 := S7 1409 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1409 ∣ 1 + 293 ^ 16).trans hd)
      have g11777 := S7 11777 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11777 ∣ 1 + 293 ^ 16).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1409 g1409 11777 g11777 (by norm_num) (by norm_num)) (by norm_num)

set_option maxHeartbeats 12000000 in
theorem zs_300 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 300 ≤ z) (hi : z < 600)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 = 8 → z ∈ ({7} : Finset ℕ)) ∧
    (e % 32 = 16 → z ∈ ({7, 41, 73, 113, 157, 167, 173, 199, 307, 449, 599, 607, 617, 643, 743, 811, 937, 967, 1201,
      1213, 1237, 1249, 1277, 1297, 1373, 1579, 1637, 1667, 1747, 1979, 2011, 2027} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 307
    · exfalso; have hd := D8 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 307 ^ 8).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 311
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 311 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 311 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 313
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 313 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g585857 := S7 585857 (by norm_num) (by norm_num) (by decide) ((by norm_num : 585857 ∣ 1 + 313 ^ 16).trans hd)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 585857 g585857 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 585857 g585857 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 317
    · exfalso; have hd := D8 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 317 ^ 8).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 317 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 331
    · exfalso; have hd := D8 he
      have g14927201 := S7 14927201 (by norm_num) (by norm_num) (by decide) ((by norm_num : 14927201 ∣ 1 + 331 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 14927201 g14927201 (by norm_num)
    · exfalso; have hd := D16 he
      have g1776833 := S7 1776833 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1776833 ∣ 1 + 331 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1776833 g1776833 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 337
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 337 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 337 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 347
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 347 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 347 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 349
    · exfalso; have hd := D8 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 349 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
    · exfalso; have hd := D16 he
      have g81409 := S7 81409 (by norm_num) (by norm_num) (by decide) ((by norm_num : 81409 ∣ 1 + 349 ^ 16).trans hd)
      have g1163 := S1 1163 (by norm_num) (by norm_num) (by decide) 81409 g81409 (by norm_num)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 1163 g1163 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 353
    · exfalso; have hd := D8 he
      have g12738353 := S7 12738353 (by norm_num) (by norm_num) (by decide) ((by norm_num : 12738353 ∣ 1 + 353 ^ 8).trans hd)
      have g229 := S1 229 (by norm_num) (by norm_num) (by decide) 12738353 g12738353 (by norm_num)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 229 g229 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 12738353 g12738353 23 g23 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g30977821093313 := S7 30977821093313 prime_30977821093313 (by norm_num) (by decide) ((by norm_num : 30977821093313 ∣ 1 + 353 ^ 16).trans hd)
      have g359 := S1 359 (by norm_num) (by norm_num) (by decide) 30977821093313 g30977821093313 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 359 g359 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 359
    · exfalso; have hd := D8 he
      have g15377 := S7 15377 (by norm_num) (by norm_num) (by decide) ((by norm_num : 15377 ∣ 1 + 359 ^ 8).trans hd)
      have g233 := S1 233 (by norm_num) (by norm_num) (by decide) 15377 g15377 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 233 g233 (by norm_num)
    · exfalso; have hd := D16 he
      have g641 := S7 641 (by norm_num) (by norm_num) (by decide) ((by norm_num : 641 ∣ 1 + 359 ^ 16).trans hd)
      have g107 := S1 107 (by norm_num) (by norm_num) (by decide) 641 g641 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 367
    · exfalso; have hd := D8 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 367 ^ 8).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
    · exfalso; have hd := D16 he
      have g2369473 := S7 2369473 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2369473 ∣ 1 + 367 ^ 16).trans hd)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 2369473 g2369473 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 29 g29 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 29 g29 5 g5 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 373
    · exfalso; have hd := D8 he
      have g187344375361201003441 := S7 187344375361201003441 prime_187344375361201003441 (by norm_num) (by decide) ((by norm_num : 187344375361201003441 ∣ 1 + 373 ^ 8).trans hd)
      have g14431 := S1 14431 (by norm_num) (by norm_num) (by decide) 187344375361201003441 g187344375361201003441 (by norm_num)
      have g3594931 := S1 3594931 (by norm_num) (by norm_num) (by decide) 187344375361201003441 g187344375361201003441 (by norm_num)
      exact absurd (S3 11 (by norm_num) (by norm_num) (by decide) 14431 g14431 3594931 g3594931 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g371873 := S7 371873 (by norm_num) (by norm_num) (by decide) ((by norm_num : 371873 ∣ 1 + 373 ^ 16).trans hd)
      have g61979 := S1 61979 (by norm_num) (by norm_num) (by decide) 371873 g371873 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 371873 g371873 61979 g61979 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 379
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 379 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g68897 := S7 68897 (by norm_num) (by norm_num) (by decide) ((by norm_num : 68897 ∣ 1 + 379 ^ 16).trans hd)
      have g11483 := S1 11483 (by norm_num) (by norm_num) (by decide) 68897 g68897 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 11483 g11483 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 383
    · exfalso; have hd := D8 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 383 ^ 8).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g641 := S7 641 (by norm_num) (by norm_num) (by decide) ((by norm_num : 641 ∣ 1 + 383 ^ 16).trans hd)
      have g107 := S1 107 (by norm_num) (by norm_num) (by decide) 641 g641 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 389
    · exfalso; have hd := D8 he
      have g23537 := S7 23537 (by norm_num) (by norm_num) (by decide) ((by norm_num : 23537 ∣ 1 + 389 ^ 8).trans hd)
      have g3923 := S1 3923 (by norm_num) (by norm_num) (by decide) 23537 g23537 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 3923 g3923 (by norm_num)
    · exfalso; have hd := D16 he
      have g18913 := S7 18913 (by norm_num) (by norm_num) (by decide) ((by norm_num : 18913 ∣ 1 + 389 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 18913 g18913 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 397
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 397 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g408501522241 := S7 408501522241 prime_408501522241 (by norm_num) (by decide) ((by norm_num : 408501522241 ∣ 1 + 397 ^ 16).trans hd)
      have g23836009 := S1 23836009 (by norm_num) (by norm_num) (by decide) 408501522241 g408501522241 (by norm_num)
      exact absurd (S3 11 (by norm_num) (by norm_num) (by decide) 408501522241 g408501522241 23836009 g23836009 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 401
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 401 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g4129 := S7 4129 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4129 ∣ 1 + 401 ^ 16).trans hd)
      have g59 := S1 59 (by norm_num) (by norm_num) (by decide) 4129 g4129 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 4129 g4129 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 409
    · exfalso; have hd := D8 he
      have g391522268549910113761 := S7 391522268549910113761 prime_391522268549910113761 (by norm_num) (by decide) ((by norm_num : 391522268549910113761 ∣ 1 + 409 ^ 8).trans hd)
      have g1291 := S1 1291 (by norm_num) (by norm_num) (by decide) 391522268549910113761 g391522268549910113761 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 1291 g1291 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g68449 := S7 68449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 68449 ∣ 1 + 409 ^ 16).trans hd)
      exact S6 37 (by norm_num) (by norm_num) (by decide) 68449 g68449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 419
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 419 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g416472899311875644799329 := S7 416472899311875644799329 prime_416472899311875644799329 (by norm_num) (by decide) ((by norm_num : 416472899311875644799329 ∣ 1 + 419 ^ 16).trans hd)
      have g101 := S1 101 (by norm_num) (by norm_num) (by decide) 416472899311875644799329 g416472899311875644799329 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 101 g101 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 421
    · exfalso; have hd := D8 he
      have g264289 := S7 264289 (by norm_num) (by norm_num) (by decide) ((by norm_num : 264289 ∣ 1 + 421 ^ 8).trans hd)
      have g107 := S1 107 (by norm_num) (by norm_num) (by decide) 264289 g264289 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
    · exfalso; have hd := D16 he
      have g1217 := S7 1217 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1217 ∣ 1 + 421 ^ 16).trans hd)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 1217 g1217 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1217 g1217 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 431
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 431 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g411361 := S7 411361 (by norm_num) (by norm_num) (by decide) ((by norm_num : 411361 ∣ 1 + 431 ^ 16).trans hd)
      have g29383 := S1 29383 (by norm_num) (by norm_num) (by decide) 411361 g411361 (by norm_num)
      have g3673 := S1 3673 (by norm_num) (by norm_num) (by decide) 29383 g29383 (by norm_num)
      have g167 := S1 167 (by norm_num) (by norm_num) (by decide) 3673 g3673 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 411361 g411361 167 g167 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 433
    · exfalso; have hd := D8 he
      have g617835950261219632321 := S7 617835950261219632321 prime_617835950261219632321 (by norm_num) (by decide) ((by norm_num : 617835950261219632321 ∣ 1 + 433 ^ 8).trans hd)
      have g308917975130609816161 := S1 308917975130609816161 prime_308917975130609816161 (by norm_num) (by decide) 617835950261219632321 g617835950261219632321 (by norm_num)
      have g154458987565304908081 := S1 154458987565304908081 prime_154458987565304908081 (by norm_num) (by decide) 308917975130609816161 g308917975130609816161 (by norm_num)
      have g293 := S1 293 (by norm_num) (by norm_num) (by decide) 154458987565304908081 g154458987565304908081 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 293 g293 (by norm_num)
    · exfalso; have hd := D16 he
      have g1889 := S7 1889 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1889 ∣ 1 + 433 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1889 g1889 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 439
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 439 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 439 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 443
    · exfalso; have hd := D8 he
      have g230251457 := S7 230251457 prime_230251457 (by norm_num) (by decide) ((by norm_num : 230251457 ∣ 1 + 443 ^ 8).trans hd)
      have g93827 := S1 93827 (by norm_num) (by norm_num) (by decide) 230251457 g230251457 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 230251457 g230251457 93827 g93827 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g1601 := S7 1601 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1601 ∣ 1 + 443 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1601 g1601 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 449
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 449 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 457
    · exfalso; have hd := D8 he
      have g61729 := S7 61729 (by norm_num) (by norm_num) (by decide) ((by norm_num : 61729 ∣ 1 + 457 ^ 8).trans hd)
      have g6173 := S1 6173 (by norm_num) (by norm_num) (by decide) 61729 g61729 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 6173 g6173 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 457 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 461
    · exfalso; have hd := D8 he
      have g307169 := S7 307169 (by norm_num) (by norm_num) (by decide) ((by norm_num : 307169 ∣ 1 + 461 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 307169 g307169 (by norm_num)
    · exfalso; have hd := D16 he
      have g5153 := S7 5153 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5153 ∣ 1 + 461 ^ 16).trans hd)
      have g859 := S1 859 (by norm_num) (by norm_num) (by decide) 5153 g5153 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 859 g859 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5153 g5153 5 g5 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 463
    · exfalso; have hd := D8 he
      have g471617 := S7 471617 (by norm_num) (by norm_num) (by decide) ((by norm_num : 471617 ∣ 1 + 463 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 471617 g471617 (by norm_num)
    · exfalso; have hd := D16 he
      have g3169 := S7 3169 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3169 ∣ 1 + 463 ^ 16).trans hd)
      have g317 := S1 317 (by norm_num) (by norm_num) (by decide) 3169 g3169 (by norm_num)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 317 g317 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 467
    · exfalso; have hd := D8 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 467 ^ 8).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g5192353 := S7 5192353 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5192353 ∣ 1 + 467 ^ 16).trans hd)
      have g557 := S1 557 (by norm_num) (by norm_num) (by decide) 5192353 g5192353 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 557 g557 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 479
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 479 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g627838273 := S7 627838273 prime_627838273 (by norm_num) (by decide) ((by norm_num : 627838273 ∣ 1 + 479 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 627838273 g627838273 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 487
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 487 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g7125761 := S7 7125761 (by norm_num) (by norm_num) (by decide) ((by norm_num : 7125761 ∣ 1 + 487 ^ 16).trans hd)
      have g169661 := S1 169661 (by norm_num) (by norm_num) (by decide) 7125761 g7125761 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 7125761 g7125761 169661 g169661 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 491
    · exfalso; have hd := D8 he
      have g1688970022366499085361 := S7 1688970022366499085361 prime_1688970022366499085361 (by norm_num) (by decide) ((by norm_num : 1688970022366499085361 ∣ 1 + 491 ^ 8).trans hd)
      have g44695037407 := S1 44695037407 prime_44695037407 (by norm_num) (by decide) 1688970022366499085361 g1688970022366499085361 (by norm_num)
      have g234467 := S1 234467 (by norm_num) (by norm_num) (by decide) 44695037407 g44695037407 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 234467 g234467 (by norm_num)
    · exfalso; have hd := D16 he
      have g6301697 := S7 6301697 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6301697 ∣ 1 + 491 ^ 16).trans hd)
      have g467 := S1 467 (by norm_num) (by norm_num) (by decide) 6301697 g6301697 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 467 g467 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 499
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 499 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g15552001 := S7 15552001 (by norm_num) (by norm_num) (by decide) ((by norm_num : 15552001 ∣ 1 + 499 ^ 16).trans hd)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 15552001 g15552001 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 503
    · exfalso; have hd := D8 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 503 ^ 8).trans hd)
    · exfalso; have hd := D16 he
      have g297545172289 := S7 297545172289 prime_297545172289 (by norm_num) (by decide) ((by norm_num : 297545172289 ∣ 1 + 503 ^ 16).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 297545172289 g297545172289 (by norm_num)
      have g77267 := S1 77267 (by norm_num) (by norm_num) (by decide) 297545172289 g297545172289 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 77267 g77267 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 509
    · exfalso; have hd := D8 he
      have g3617 := S7 3617 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3617 ∣ 1 + 509 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 3617 g3617 (by norm_num)
    · exfalso; have hd := D16 he
      have g56897201427233 := S7 56897201427233 prime_56897201427233 (by norm_num) (by decide) ((by norm_num : 56897201427233 ∣ 1 + 509 ^ 16).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 56897201427233 g56897201427233 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 521
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 521 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g307201 := S7 307201 (by norm_num) (by norm_num) (by decide) ((by norm_num : 307201 ∣ 1 + 521 ^ 16).trans hd)
      have g21943 := S1 21943 (by norm_num) (by norm_num) (by decide) 307201 g307201 (by norm_num)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 21943 g21943 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 307201 g307201 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 523
    · exfalso; have hd := D8 he
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 523 ^ 8).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 113 g113 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 113 g113 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g1533437457473 := S7 1533437457473 prime_1533437457473 (by norm_num) (by decide) ((by norm_num : 1533437457473 ∣ 1 + 523 ^ 16).trans hd)
      have g1007299 := S1 1007299 (by norm_num) (by norm_num) (by decide) 1533437457473 g1533437457473 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 1007299 g1007299 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 541
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 541 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g929 := S7 929 (by norm_num) (by norm_num) (by decide) ((by norm_num : 929 ∣ 1 + 541 ^ 16).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 929 g929 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 929 g929 5 g5 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 547
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 547 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1141723489 := S7 1141723489 prime_1141723489 (by norm_num) (by decide) ((by norm_num : 1141723489 ∣ 1 + 547 ^ 16).trans hd)
      have g193841 := S1 193841 (by norm_num) (by norm_num) (by decide) 1141723489 g1141723489 (by norm_num)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 193841 g193841 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 557
    · exfalso; have hd := D8 he
      have g4632458802461936442001 := S7 4632458802461936442001 prime_4632458802461936442001 (by norm_num) (by decide) ((by norm_num : 4632458802461936442001 ∣ 1 + 557 ^ 8).trans hd)
      have g9733 := S1 9733 (by norm_num) (by norm_num) (by decide) 4632458802461936442001 g4632458802461936442001 (by norm_num)
      exact absurd (S3 157 (by norm_num) (by norm_num) (by decide) 4632458802461936442001 g4632458802461936442001 9733 g9733 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g22721 := S7 22721 (by norm_num) (by norm_num) (by decide) ((by norm_num : 22721 ∣ 1 + 557 ^ 16).trans hd)
      have g541 := S1 541 (by norm_num) (by norm_num) (by decide) 22721 g22721 (by norm_num)
      have g271 := S1 271 (by norm_num) (by norm_num) (by decide) 541 g541 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 271 g271 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 563
    · exfalso; have hd := D8 he
      have g159805526897 := S7 159805526897 prime_159805526897 (by norm_num) (by decide) ((by norm_num : 159805526897 ∣ 1 + 563 ^ 8).trans hd)
      have g208277 := S1 208277 (by norm_num) (by norm_num) (by decide) 159805526897 g159805526897 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 208277 g208277 (by norm_num)
    · exfalso; have hd := D16 he
      have g291041 := S7 291041 (by norm_num) (by norm_num) (by decide) ((by norm_num : 291041 ∣ 1 + 563 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 291041 g291041 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 569
    · exfalso; have hd := D8 he
      have g288529 := S7 288529 (by norm_num) (by norm_num) (by decide) ((by norm_num : 288529 ∣ 1 + 569 ^ 8).trans hd)
      have g43 := S1 43 (by norm_num) (by norm_num) (by decide) 288529 g288529 (by norm_num)
      exact absurd (S3 11 (by norm_num) (by norm_num) (by decide) 288529 g288529 43 g43 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g3329 := S7 3329 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3329 ∣ 1 + 569 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 3329 g3329 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 571
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 571 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 571 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 577
    · exfalso; have hd := D8 he
      have g6142943339981990979841 := S7 6142943339981990979841 prime_6142943339981990979841 (by norm_num) (by decide) ((by norm_num : 6142943339981990979841 ∣ 1 + 577 ^ 8).trans hd)
      have g11131 := S1 11131 (by norm_num) (by norm_num) (by decide) 6142943339981990979841 g6142943339981990979841 (by norm_num)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 11131 g11131 (by norm_num)
    · exfalso; have hd := D16 he
      have g1370177 := S7 1370177 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1370177 ∣ 1 + 577 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1370177 g1370177 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 587
    · exfalso; have hd := D8 he
      have g13841 := S7 13841 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13841 ∣ 1 + 587 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 13841 g13841 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 587 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 593
    · exfalso; have hd := D8 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 593 ^ 8).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
    · exfalso; have hd := D16 he
      have g10529 := S7 10529 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10529 ∣ 1 + 593 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 10529 g10529 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 599
    · exfalso; have hd := D8 he
      have g1249 := S7 1249 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1249 ∣ 1 + 599 ^ 8).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 1249 g1249 (by norm_num)
    · simp

set_option maxHeartbeats 12000000 in
theorem zs_600 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 600 ≤ z) (hi : z < 900)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 = 8 → z ∈ ({7} : Finset ℕ)) ∧
    (e % 32 = 16 → z ∈ ({7, 41, 73, 113, 157, 167, 173, 199, 307, 449, 599, 607, 617, 643, 743, 811, 937, 967, 1201,
      1213, 1237, 1249, 1277, 1297, 1373, 1579, 1637, 1667, 1747, 1979, 2011, 2027} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 601
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 601 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 601 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 607
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 607 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 613
    · exfalso; have hd := D8 he
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 613 ^ 8).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 113 g113 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 113 g113 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g240382049 := S7 240382049 prime_240382049 (by norm_num) (by decide) ((by norm_num : 240382049 ∣ 1 + 613 ^ 16).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 240382049 g240382049 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 617
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 617 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 619
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 619 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g55825839073 := S7 55825839073 prime_55825839073 (by norm_num) (by decide) ((by norm_num : 55825839073 ∣ 1 + 619 ^ 16).trans hd)
      have g397 := S1 397 (by norm_num) (by norm_num) (by decide) 55825839073 g55825839073 (by norm_num)
      have g199 := S1 199 (by norm_num) (by norm_num) (by decide) 397 g397 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 199 g199 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 631
    · exfalso; have hd := D8 he
      have g304237489 := S7 304237489 prime_304237489 (by norm_num) (by decide) ((by norm_num : 304237489 ∣ 1 + 631 ^ 8).trans hd)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 304237489 g304237489 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D16 he
      have g641 := S7 641 (by norm_num) (by norm_num) (by decide) ((by norm_num : 641 ∣ 1 + 631 ^ 16).trans hd)
      have g107 := S1 107 (by norm_num) (by norm_num) (by decide) 641 g641 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 641
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 641 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1153 := S7 1153 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1153 ∣ 1 + 641 ^ 16).trans hd)
      have g577 := S1 577 (by norm_num) (by norm_num) (by decide) 1153 g1153 (by norm_num)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 643
    · exfalso; have hd := D8 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 643 ^ 8).trans hd)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 647
    · exfalso; have hd := D8 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 647 ^ 8).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
    · exfalso; have hd := D16 he
      have g2491457 := S7 2491457 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2491457 ∣ 1 + 647 ^ 16).trans hd)
      have g241 := S1 241 (by norm_num) (by norm_num) (by decide) 2491457 g2491457 (by norm_num)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 653
    · exfalso; have hd := D8 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 653 ^ 8).trans hd)
    · exfalso; have hd := D16 he
      have g165857 := S7 165857 (by norm_num) (by norm_num) (by decide) ((by norm_num : 165857 ∣ 1 + 653 ^ 16).trans hd)
      have g359 := S1 359 (by norm_num) (by norm_num) (by decide) 165857 g165857 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 359 g359 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 659
    · exfalso; have hd := D8 he
      have g240257 := S7 240257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 240257 ∣ 1 + 659 ^ 8).trans hd)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 240257 g240257 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 240257 g240257 23 g23 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g75329 := S7 75329 (by norm_num) (by norm_num) (by decide) ((by norm_num : 75329 ∣ 1 + 659 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 75329 g75329 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 661
    · exfalso; have hd := D8 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 661 ^ 8).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g378512609 := S7 378512609 prime_378512609 (by norm_num) (by decide) ((by norm_num : 378512609 ∣ 1 + 661 ^ 16).trans hd)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 378512609 g378512609 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 378512609 g378512609 23 g23 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 673
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 673 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g56417 := S7 56417 (by norm_num) (by norm_num) (by decide) ((by norm_num : 56417 ∣ 1 + 673 ^ 16).trans hd)
      have g9403 := S1 9403 (by norm_num) (by norm_num) (by decide) 56417 g56417 (by norm_num)
      have g2351 := S1 2351 (by norm_num) (by norm_num) (by decide) 9403 g9403 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 2351 g2351 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 677
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 677 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 677 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 683
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 683 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g58049 := S7 58049 (by norm_num) (by norm_num) (by decide) ((by norm_num : 58049 ∣ 1 + 683 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 58049 g58049 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 691
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 691 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g88501729 := S7 88501729 prime_88501729 (by norm_num) (by decide) ((by norm_num : 88501729 ∣ 1 + 691 ^ 16).trans hd)
      have g557 := S1 557 (by norm_num) (by norm_num) (by decide) 88501729 g88501729 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 557 g557 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 701
    · exfalso; have hd := D8 he
      have g3839872682369 := S7 3839872682369 prime_3839872682369 (by norm_num) (by decide) ((by norm_num : 3839872682369 ∣ 1 + 701 ^ 8).trans hd)
      exact S6 23 (by norm_num) (by norm_num) (by decide) 3839872682369 g3839872682369 (by norm_num)
    · exfalso; have hd := D16 he
      have g929 := S7 929 (by norm_num) (by norm_num) (by decide) ((by norm_num : 929 ∣ 1 + 701 ^ 16).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 929 g929 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 929 g929 5 g5 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 709
    · exfalso; have hd := D8 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 709 ^ 8).trans hd)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 709 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 719
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 719 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g8971453889 := S7 8971453889 prime_8971453889 (by norm_num) (by decide) ((by norm_num : 8971453889 ∣ 1 + 719 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 8971453889 g8971453889 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 727
    · exfalso; have hd := D8 he
      have g32103713 := S7 32103713 (by norm_num) (by norm_num) (by decide) ((by norm_num : 32103713 ∣ 1 + 727 ^ 8).trans hd)
      have g124433 := S1 124433 (by norm_num) (by norm_num) (by decide) 32103713 g32103713 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 124433 g124433 (by norm_num)
    · exfalso; have hd := D16 he
      have g286260692257 := S7 286260692257 prime_286260692257 (by norm_num) (by decide) ((by norm_num : 286260692257 ∣ 1 + 727 ^ 16).trans hd)
      have g2663 := S1 2663 (by norm_num) (by norm_num) (by decide) 286260692257 g286260692257 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2663 g2663 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 733
    · exfalso; have hd := D8 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 733 ^ 8).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · exfalso; have hd := D16 he
      have g32993 := S7 32993 (by norm_num) (by norm_num) (by decide) ((by norm_num : 32993 ∣ 1 + 733 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 32993 g32993 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 739
    · exfalso; have hd := D8 he
      have g1889 := S7 1889 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1889 ∣ 1 + 739 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1889 g1889 (by norm_num)
    · exfalso; have hd := D16 he
      have g15802442706594785921 := S7 15802442706594785921 prime_15802442706594785921 (by norm_num) (by decide) ((by norm_num : 15802442706594785921 ∣ 1 + 739 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 15802442706594785921 g15802442706594785921 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 743
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 743 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 751
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 751 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g2577111937 := S7 2577111937 prime_2577111937 (by norm_num) (by decide) ((by norm_num : 2577111937 ∣ 1 + 751 ^ 16).trans hd)
      have g34825837 := S1 34825837 (by norm_num) (by norm_num) (by decide) 2577111937 g2577111937 (by norm_num)
      have g17412919 := S1 17412919 (by norm_num) (by norm_num) (by decide) 34825837 g34825837 (by norm_num)
      have g62189 := S1 62189 (by norm_num) (by norm_num) (by decide) 17412919 g17412919 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 62189 g62189 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 757
    · exfalso; have hd := D8 he
      have g495377 := S7 495377 (by norm_num) (by norm_num) (by decide) ((by norm_num : 495377 ∣ 1 + 757 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 495377 g495377 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 757 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 761
    · exfalso; have hd := D8 he
      have g54049 := S7 54049 (by norm_num) (by norm_num) (by decide) ((by norm_num : 54049 ∣ 1 + 761 ^ 8).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 54049 g54049 (by norm_num)
    · exfalso; have hd := D16 he
      have g5417953 := S7 5417953 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5417953 ∣ 1 + 761 ^ 16).trans hd)
      have g109 := S1 109 (by norm_num) (by norm_num) (by decide) 5417953 g5417953 (by norm_num)
      have g857 := S1 857 (by norm_num) (by norm_num) (by decide) 5417953 g5417953 (by norm_num)
      exact absurd (S3 11 (by norm_num) (by norm_num) (by decide) 109 g109 857 g857 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 769
    · exfalso; have hd := D8 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 769 ^ 8).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g4056769 := S7 4056769 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4056769 ∣ 1 + 769 ^ 16).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 4056769 g4056769 (by norm_num)
      have g405677 := S1 405677 (by norm_num) (by norm_num) (by decide) 4056769 g4056769 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 405677 g405677 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 773
    · exfalso; have hd := D8 he
      have g144593 := S7 144593 (by norm_num) (by norm_num) (by decide) ((by norm_num : 144593 ∣ 1 + 773 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 144593 g144593 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := S7 353 (by norm_num) (by norm_num) (by decide) ((by norm_num : 353 ∣ 1 + 773 ^ 16).trans hd)
      have g59 := S1 59 (by norm_num) (by norm_num) (by decide) 353 g353 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 353 g353 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 787
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 787 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g673 := S7 673 (by norm_num) (by norm_num) (by decide) ((by norm_num : 673 ∣ 1 + 787 ^ 16).trans hd)
      have g337 := S1 337 (by norm_num) (by norm_num) (by decide) 673 g673 (by norm_num)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 797
    · exfalso; have hd := D8 he
      have g258426017 := S7 258426017 prime_258426017 (by norm_num) (by decide) ((by norm_num : 258426017 ∣ 1 + 797 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 258426017 g258426017 (by norm_num)
    · exfalso; have hd := D16 he
      have g3329 := S7 3329 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3329 ∣ 1 + 797 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 3329 g3329 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 809
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 809 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g118273 := S7 118273 (by norm_num) (by norm_num) (by decide) ((by norm_num : 118273 ∣ 1 + 809 ^ 16).trans hd)
      have g4549 := S1 4549 (by norm_num) (by norm_num) (by decide) 118273 g118273 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 4549 g4549 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 811
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 811 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 821
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 821 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 821 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 823
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 823 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g98017 := S7 98017 (by norm_num) (by norm_num) (by decide) ((by norm_num : 98017 ∣ 1 + 823 ^ 16).trans hd)
      have g49009 := S1 49009 (by norm_num) (by norm_num) (by decide) 98017 g98017 (by norm_num)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 49009 g49009 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 827
    · exfalso; have hd := D8 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 827 ^ 8).trans hd)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 827 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 829
    · exfalso; have hd := D8 he
      have g5025697 := S7 5025697 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5025697 ∣ 1 + 829 ^ 8).trans hd)
      have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 5025697 g5025697 (by norm_num)
      have g167 := S1 167 (by norm_num) (by norm_num) (by decide) 5025697 g5025697 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 41 g41 167 g167 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g41890299939361 := S7 41890299939361 prime_41890299939361 (by norm_num) (by decide) ((by norm_num : 41890299939361 ∣ 1 + 829 ^ 16).trans hd)
      have g207199 := S1 207199 (by norm_num) (by norm_num) (by decide) 41890299939361 g41890299939361 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 207199 g207199 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 839
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 839 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 839 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 853
    · exfalso; have hd := D8 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 853 ^ 8).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
    · exfalso; have hd := D16 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 853 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 857
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 857 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g73121 := S7 73121 (by norm_num) (by norm_num) (by decide) ((by norm_num : 73121 ∣ 1 + 857 ^ 16).trans hd)
      have g1741 := S1 1741 (by norm_num) (by norm_num) (by decide) 73121 g73121 (by norm_num)
      have g13 := S1 13 (by norm_num) (by norm_num) (by decide) 1741 g1741 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 73121 g73121 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 859
    · exfalso; have hd := D8 he
      have g148222903052887857582961 := S7 148222903052887857582961 prime_148222903052887857582961 (by norm_num) (by decide) ((by norm_num : 148222903052887857582961 ∣ 1 + 859 ^ 8).trans hd)
      have g5844802782997 := S1 5844802782997 prime_5844802782997 (by norm_num) (by decide) 148222903052887857582961 g148222903052887857582961 (by norm_num)
      exact absurd (S3 31 (by norm_num) (by norm_num) (by decide) 148222903052887857582961 g148222903052887857582961 5844802782997 g5844802782997 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g527489 := S7 527489 (by norm_num) (by norm_num) (by decide) ((by norm_num : 527489 ∣ 1 + 859 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 527489 g527489 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 863
    · exfalso; have hd := D8 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 863 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
    · exfalso; have hd := D16 he
      have g1617697 := S7 1617697 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1617697 ∣ 1 + 863 ^ 16).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 1617697 g1617697 (by norm_num)
      have g42571 := S1 42571 (by norm_num) (by norm_num) (by decide) 1617697 g1617697 (by norm_num)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 42571 g42571 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 19 g19 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 877
    · exfalso; have hd := D8 he
      have g1159649 := S7 1159649 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1159649 ∣ 1 + 877 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1159649 g1159649 (by norm_num)
    · exfalso; have hd := D16 he
      have g6097313 := S7 6097313 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6097313 ∣ 1 + 877 ^ 16).trans hd)
      have g23633 := S1 23633 (by norm_num) (by norm_num) (by decide) 6097313 g6097313 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 23633 g23633 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 881
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 881 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g614177 := S7 614177 (by norm_num) (by norm_num) (by decide) ((by norm_num : 614177 ∣ 1 + 881 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 614177 g614177 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 883
    · exfalso; have hd := D8 he
      have g929 := S7 929 (by norm_num) (by norm_num) (by decide) ((by norm_num : 929 ∣ 1 + 883 ^ 8).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 929 g929 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 929 g929 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g10529 := S7 10529 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10529 ∣ 1 + 883 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 10529 g10529 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 887
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 887 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1292767882369 := S7 1292767882369 prime_1292767882369 (by norm_num) (by decide) ((by norm_num : 1292767882369 ∣ 1 + 887 ^ 16).trans hd)
      have g283 := S1 283 (by norm_num) (by norm_num) (by decide) 1292767882369 g1292767882369 (by norm_num)
      have g71 := S1 71 (by norm_num) (by norm_num) (by decide) 283 g283 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)

set_option maxHeartbeats 12000000 in
theorem zs_900 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 900 ≤ z) (hi : z < 1200)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 = 8 → z ∈ ({7} : Finset ℕ)) ∧
    (e % 32 = 16 → z ∈ ({7, 41, 73, 113, 157, 167, 173, 199, 307, 449, 599, 607, 617, 643, 743, 811, 937, 967, 1201,
      1213, 1237, 1249, 1277, 1297, 1373, 1579, 1637, 1667, 1747, 1979, 2011, 2027} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 907
    · exfalso; have hd := D8 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 907 ^ 8).trans hd)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 907 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 911
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 911 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g25121 := S7 25121 (by norm_num) (by norm_num) (by decide) ((by norm_num : 25121 ∣ 1 + 911 ^ 16).trans hd)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 25121 g25121 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 919
    · exfalso; have hd := D8 he
      have g2142577 := S7 2142577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2142577 ∣ 1 + 919 ^ 8).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 2142577 g2142577 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 919 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 929
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 929 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g2777441 := S7 2777441 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2777441 ∣ 1 + 929 ^ 16).trans hd)
      have g12511 := S1 12511 (by norm_num) (by norm_num) (by decide) 2777441 g2777441 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 12511 g12511 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 937
    · exfalso; have hd := D8 he
      have g16295777 := S7 16295777 (by norm_num) (by norm_num) (by decide) ((by norm_num : 16295777 ∣ 1 + 937 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 16295777 g16295777 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 941
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 941 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 941 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 947
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 947 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g4091777 := S7 4091777 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4091777 ∣ 1 + 947 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 4091777 g4091777 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 953
    · exfalso; have hd := D8 he
      have g14177 := S7 14177 (by norm_num) (by norm_num) (by decide) ((by norm_num : 14177 ∣ 1 + 953 ^ 8).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 14177 g14177 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g112097 := S7 112097 (by norm_num) (by norm_num) (by decide) ((by norm_num : 112097 ∣ 1 + 953 ^ 16).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 112097 g112097 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 967
    · exfalso; have hd := D8 he
      have g10529 := S7 10529 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10529 ∣ 1 + 967 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 10529 g10529 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 971
    · exfalso; have hd := D8 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 971 ^ 8).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · exfalso; have hd := D16 he
      have g14657 := S7 14657 (by norm_num) (by norm_num) (by decide) ((by norm_num : 14657 ∣ 1 + 971 ^ 16).trans hd)
      have g349 := S1 349 (by norm_num) (by norm_num) (by decide) 14657 g14657 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 349 g349 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 977
    · exfalso; have hd := D8 he
      have g593 := S7 593 (by norm_num) (by norm_num) (by decide) ((by norm_num : 593 ∣ 1 + 977 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 593 g593 (by norm_num)
    · exfalso; have hd := D16 he
      have g577 := S7 577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 577 ∣ 1 + 977 ^ 16).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 983
    · exfalso; have hd := D8 he
      have g577 := S7 577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 577 ∣ 1 + 983 ^ 8).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
    · exfalso; have hd := D16 he
      have g5441 := S7 5441 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5441 ∣ 1 + 983 ^ 16).trans hd)
      have g907 := S1 907 (by norm_num) (by norm_num) (by decide) 5441 g5441 (by norm_num)
      have g227 := S1 227 (by norm_num) (by norm_num) (by decide) 907 g907 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5441 g5441 227 g227 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 991
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 991 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g577 := S7 577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 577 ∣ 1 + 991 ^ 16).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 997
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 997 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g180289 := S7 180289 (by norm_num) (by norm_num) (by decide) ((by norm_num : 180289 ∣ 1 + 997 ^ 16).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 180289 g180289 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1009
    · exfalso; have hd := D8 he
      have g15137 := S7 15137 (by norm_num) (by norm_num) (by decide) ((by norm_num : 15137 ∣ 1 + 1009 ^ 8).trans hd)
      exact S6 29 (by norm_num) (by norm_num) (by decide) 15137 g15137 (by norm_num)
    · exfalso; have hd := D16 he
      have g36929 := S7 36929 (by norm_num) (by norm_num) (by decide) ((by norm_num : 36929 ∣ 1 + 1009 ^ 16).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 36929 g36929 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 36929 g36929 5 g5 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1013
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1013 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g3041 := S7 3041 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3041 ∣ 1 + 1013 ^ 16).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 3041 g3041 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1019
    · exfalso; have hd := D8 he
      have g1409 := S7 1409 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1409 ∣ 1 + 1019 ^ 8).trans hd)
      have g47 := S1 47 (by norm_num) (by norm_num) (by decide) 1409 g1409 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1409 g1409 47 g47 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g15910619201 := S7 15910619201 prime_15910619201 (by norm_num) (by decide) ((by norm_num : 15910619201 ∣ 1 + 1019 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 15910619201 g15910619201 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1021
    · exfalso; have hd := D8 he
      have g590440230397776959593681 := S7 590440230397776959593681 prime_590440230397776959593681 (by norm_num) (by decide) ((by norm_num : 590440230397776959593681 ∣ 1 + 1021 ^ 8).trans hd)
      have g3331 := S1 3331 (by norm_num) (by norm_num) (by decide) 590440230397776959593681 g590440230397776959593681 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 3331 g3331 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1021 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1031
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1031 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g3361 := S7 3361 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3361 ∣ 1 + 1031 ^ 16).trans hd)
      exact S6 41 (by norm_num) (by norm_num) (by decide) 3361 g3361 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1033
    · exfalso; have hd := D8 he
      have g753732192488350417 := S7 753732192488350417 prime_753732192488350417 (by norm_num) (by decide) ((by norm_num : 753732192488350417 ∣ 1 + 1033 ^ 8).trans hd)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 753732192488350417 g753732192488350417 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1033 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1039
    · exfalso; have hd := D8 he
      have g2746481 := S7 2746481 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2746481 ∣ 1 + 1039 ^ 8).trans hd)
      have g167 := S1 167 (by norm_num) (by norm_num) (by decide) 2746481 g2746481 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 2746481 g2746481 167 g167 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1039 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1049
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1049 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g13633 := S7 13633 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13633 ∣ 1 + 1049 ^ 16).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 13633 g13633 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1051
    · exfalso; have hd := D8 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 1051 ^ 8).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · exfalso; have hd := D16 he
      have g20129 := S7 20129 (by norm_num) (by norm_num) (by decide) ((by norm_num : 20129 ∣ 1 + 1051 ^ 16).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 20129 g20129 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 20129 g20129 11 g11 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1061
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1061 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g16993 := S7 16993 (by norm_num) (by norm_num) (by decide) ((by norm_num : 16993 ∣ 1 + 1061 ^ 16).trans hd)
      have g293 := S1 293 (by norm_num) (by norm_num) (by decide) 16993 g16993 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 293 g293 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1063
    · exfalso; have hd := D8 he
      have g4507537 := S7 4507537 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4507537 ∣ 1 + 1063 ^ 8).trans hd)
      have g811 := S1 811 (by norm_num) (by norm_num) (by decide) 4507537 g4507537 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 4507537 g4507537 811 g811 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g1303421777703592289 := S7 1303421777703592289 prime_1303421777703592289 (by norm_num) (by decide) ((by norm_num : 1303421777703592289 ∣ 1 + 1063 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1303421777703592289 g1303421777703592289 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1069
    · exfalso; have hd := D8 he
      have g37303841 := S7 37303841 (by norm_num) (by norm_num) (by decide) ((by norm_num : 37303841 ∣ 1 + 1069 ^ 8).trans hd)
      have g6217307 := S1 6217307 (by norm_num) (by norm_num) (by decide) 37303841 g37303841 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 6217307 g6217307 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := S7 353 (by norm_num) (by norm_num) (by decide) ((by norm_num : 353 ∣ 1 + 1069 ^ 16).trans hd)
      have g59 := S1 59 (by norm_num) (by norm_num) (by decide) 353 g353 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 353 g353 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1087
    · exfalso; have hd := D8 he
      have g243553 := S7 243553 (by norm_num) (by norm_num) (by decide) ((by norm_num : 243553 ∣ 1 + 1087 ^ 8).trans hd)
      have g2591 := S1 2591 (by norm_num) (by norm_num) (by decide) 243553 g243553 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2591 g2591 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1087 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1091
    · exfalso; have hd := D8 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 1091 ^ 8).trans hd)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 1091 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1093
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1093 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g2081 := S7 2081 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2081 ∣ 1 + 1093 ^ 16).trans hd)
      have g347 := S1 347 (by norm_num) (by norm_num) (by decide) 2081 g2081 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 2081 g2081 347 g347 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1097
    · exfalso; have hd := D8 he
      have g236993 := S7 236993 (by norm_num) (by norm_num) (by decide) ((by norm_num : 236993 ∣ 1 + 1097 ^ 8).trans hd)
      have g39499 := S1 39499 (by norm_num) (by norm_num) (by decide) 236993 g236993 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 39499 g39499 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1097 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1103
    · exfalso; have hd := D8 he
      have g1095403448591351982886081 := S7 1095403448591351982886081 prime_1095403448591351982886081 (by norm_num) (by decide) ((by norm_num : 1095403448591351982886081 ∣ 1 + 1103 ^ 8).trans hd)
      have g3889 := S1 3889 (by norm_num) (by norm_num) (by decide) 1095403448591351982886081 g1095403448591351982886081 (by norm_num)
      have g28069 := S1 28069 (by norm_num) (by norm_num) (by decide) 1095403448591351982886081 g1095403448591351982886081 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 3889 g3889 28069 g28069 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g3655444202623937 := S7 3655444202623937 prime_3655444202623937 (by norm_num) (by decide) ((by norm_num : 3655444202623937 ∣ 1 + 1103 ^ 16).trans hd)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 3655444202623937 g3655444202623937 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1109
    · exfalso; have hd := D8 he
      have g18295290017 := S7 18295290017 prime_18295290017 (by norm_num) (by decide) ((by norm_num : 18295290017 ∣ 1 + 1109 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 18295290017 g18295290017 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1109 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1117
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1117 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g13921 := S7 13921 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13921 ∣ 1 + 1117 ^ 16).trans hd)
      have g6961 := S1 6961 (by norm_num) (by norm_num) (by decide) 13921 g13921 (by norm_num)
      exact S6 59 (by norm_num) (by norm_num) (by decide) 6961 g6961 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1123
    · exfalso; have hd := D8 he
      have g3169 := S7 3169 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3169 ∣ 1 + 1123 ^ 8).trans hd)
      have g317 := S1 317 (by norm_num) (by norm_num) (by decide) 3169 g3169 (by norm_num)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 317 g317 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D16 he
      have g340321 := S7 340321 (by norm_num) (by norm_num) (by decide) ((by norm_num : 340321 ∣ 1 + 1123 ^ 16).trans hd)
      have g647 := S1 647 (by norm_num) (by norm_num) (by decide) 340321 g340321 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 647 g647 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1129
    · exfalso; have hd := D8 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 1129 ^ 8).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
    · exfalso; have hd := D16 he
      have g4673 := S7 4673 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4673 ∣ 1 + 1129 ^ 16).trans hd)
      have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 4673 g4673 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 4673 g4673 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1151
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1151 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g273324847753057 := S7 273324847753057 prime_273324847753057 (by norm_num) (by decide) ((by norm_num : 273324847753057 ∣ 1 + 1151 ^ 16).trans hd)
      have g759911 := S1 759911 (by norm_num) (by norm_num) (by decide) 273324847753057 g273324847753057 (by norm_num)
      have g31663 := S1 31663 (by norm_num) (by norm_num) (by decide) 759911 g759911 (by norm_num)
      have g1979 := S1 1979 (by norm_num) (by norm_num) (by decide) 31663 g31663 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1979 g1979 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1153
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1153 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g4289 := S7 4289 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4289 ∣ 1 + 1153 ^ 16).trans hd)
      have g639937 := S7 639937 (by norm_num) (by norm_num) (by decide) ((by norm_num : 639937 ∣ 1 + 1153 ^ 16).trans hd)
      exact absurd (S3 13 (by norm_num) (by norm_num) (by decide) 4289 g4289 639937 g639937 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1163
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1163 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1249 := S7 1249 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1249 ∣ 1 + 1163 ^ 16).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 1249 g1249 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1171
    · exfalso; have hd := D8 he
      have g305521 := S7 305521 (by norm_num) (by norm_num) (by decide) ((by norm_num : 305521 ∣ 1 + 1171 ^ 8).trans hd)
      have g139 := S1 139 (by norm_num) (by norm_num) (by decide) 305521 g305521 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 305521 g305521 139 g139 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g280129 := S7 280129 (by norm_num) (by norm_num) (by decide) ((by norm_num : 280129 ∣ 1 + 1171 ^ 16).trans hd)
      have g1790209 := S7 1790209 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1790209 ∣ 1 + 1171 ^ 16).trans hd)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 280129 g280129 1790209 g1790209 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1181
    · exfalso; have hd := D8 he
      have g577 := S7 577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 577 ∣ 1 + 1181 ^ 8).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 1181 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1187
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1187 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g577 := S7 577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 577 ∣ 1 + 1187 ^ 16).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1193
    · exfalso; have hd := D8 he
      have g214433 := S7 214433 (by norm_num) (by norm_num) (by decide) ((by norm_num : 214433 ∣ 1 + 1193 ^ 8).trans hd)
      exact S6 19 (by norm_num) (by norm_num) (by decide) 214433 g214433 (by norm_num)
    · exfalso; have hd := D16 he
      have g2081 := S7 2081 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2081 ∣ 1 + 1193 ^ 16).trans hd)
      have g1243841 := S7 1243841 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1243841 ∣ 1 + 1193 ^ 16).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 2081 g2081 1243841 g1243841 (by norm_num) (by norm_num)) (by norm_num)

set_option maxHeartbeats 12000000 in
theorem zs_1200 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1200 ≤ z) (hi : z < 1500)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 = 8 → z ∈ ({7} : Finset ℕ)) ∧
    (e % 32 = 16 → z ∈ ({7, 41, 73, 113, 157, 167, 173, 199, 307, 449, 599, 607, 617, 643, 743, 811, 937, 967, 1201,
      1213, 1237, 1249, 1277, 1297, 1373, 1579, 1637, 1667, 1747, 1979, 2011, 2027} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1201
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1201 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1213
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1213 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1217
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1217 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := S7 257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 257 ∣ 1 + 1217 ^ 16).trans hd)
      have g43 := S1 43 (by norm_num) (by norm_num) (by decide) 257 g257 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 43 g43 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 257 g257 11 g11 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1223
    · exfalso; have hd := D8 he
      have g297457729 := S7 297457729 prime_297457729 (by norm_num) (by decide) ((by norm_num : 297457729 ∣ 1 + 1223 ^ 8).trans hd)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 297457729 g297457729 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D16 he
      have g11982913 := S7 11982913 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11982913 ∣ 1 + 1223 ^ 16).trans hd)
      have g5991457 := S1 5991457 (by norm_num) (by norm_num) (by decide) 11982913 g11982913 (by norm_num)
      have g9391 := S1 9391 (by norm_num) (by norm_num) (by decide) 5991457 g5991457 (by norm_num)
      have g587 := S1 587 (by norm_num) (by norm_num) (by decide) 9391 g9391 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 587 g587 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1229
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1229 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g256085953 := S7 256085953 prime_256085953 (by norm_num) (by decide) ((by norm_num : 256085953 ∣ 1 + 1229 ^ 16).trans hd)
      have g853 := S1 853 (by norm_num) (by norm_num) (by decide) 256085953 g256085953 (by norm_num)
      have g4057 := S1 4057 (by norm_num) (by norm_num) (by decide) 256085953 g256085953 (by norm_num)
      have g2029 := S1 2029 (by norm_num) (by norm_num) (by decide) 4057 g4057 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 853 g853 2029 g2029 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1231
    · exfalso; have hd := D8 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 1231 ^ 8).trans hd)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1231 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1237
    · exfalso; have hd := D8 he
      have g19854587986529 := S7 19854587986529 prime_19854587986529 (by norm_num) (by decide) ((by norm_num : 19854587986529 ∣ 1 + 1237 ^ 8).trans hd)
      have g2139367 := S1 2139367 (by norm_num) (by norm_num) (by decide) 19854587986529 g19854587986529 (by norm_num)
      exact absurd (S3 11 (by norm_num) (by norm_num) (by decide) 19854587986529 g19854587986529 2139367 g2139367 (by norm_num) (by norm_num)) (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1249
    · exfalso; have hd := D8 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 1249 ^ 8).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1259
    · exfalso; have hd := D8 he
      have g4225841 := S7 4225841 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4225841 ∣ 1 + 1259 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 4225841 g4225841 (by norm_num)
    · exfalso; have hd := D16 he
      have g19154081 := S7 19154081 (by norm_num) (by norm_num) (by decide) ((by norm_num : 19154081 ∣ 1 + 1259 ^ 16).trans hd)
      have g3192347 := S1 3192347 (by norm_num) (by norm_num) (by decide) 19154081 g19154081 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 19154081 g19154081 3192347 g3192347 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1277
    · exfalso; have hd := D8 he
      have g257 := S7 257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 257 ∣ 1 + 1277 ^ 8).trans hd)
      have g43 := S1 43 (by norm_num) (by norm_num) (by decide) 257 g257 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 43 g43 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 257 g257 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1279
    · exfalso; have hd := D8 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1279 ^ 8).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 1279 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1283
    · exfalso; have hd := D8 he
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 1283 ^ 8).trans hd)
      have g257 := S7 257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 257 ∣ 1 + 1283 ^ 8).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 113 g113 257 g257 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g27361 := S7 27361 (by norm_num) (by norm_num) (by decide) ((by norm_num : 27361 ∣ 1 + 1283 ^ 16).trans hd)
      have g13681 := S1 13681 (by norm_num) (by norm_num) (by decide) 27361 g27361 (by norm_num)
      have g6841 := S1 6841 (by norm_num) (by norm_num) (by decide) 13681 g13681 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 6841 g6841 (by norm_num)
      have g311 := S1 311 (by norm_num) (by norm_num) (by decide) 6841 g6841 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 11 g11 311 g311 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1289
    · exfalso; have hd := D8 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 1289 ^ 8).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · exfalso; have hd := D16 he
      have g13121 := S7 13121 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13121 ∣ 1 + 1289 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 13121 g13121 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1291
    · exfalso; have hd := D8 he
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 1291 ^ 8).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 113 g113 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 113 g113 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1291 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1297
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1297 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1301
    · exfalso; have hd := D8 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 1301 ^ 8).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g21543265124993 := S7 21543265124993 prime_21543265124993 (by norm_num) (by decide) ((by norm_num : 21543265124993 ∣ 1 + 1301 ^ 16).trans hd)
      have g113 := S1 113 (by norm_num) (by norm_num) (by decide) 21543265124993 g21543265124993 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 21543265124993 g21543265124993 113 g113 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1303
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1303 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1303 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1307
    · exfalso; have hd := D8 he
      have g4257696543602770772646001 := S7 4257696543602770772646001 prime_4257696543602770772646001 (by norm_num) (by decide) ((by norm_num : 4257696543602770772646001 ∣ 1 + 1307 ^ 8).trans hd)
      have g57679 := S1 57679 (by norm_num) (by norm_num) (by decide) 4257696543602770772646001 g4257696543602770772646001 (by norm_num)
      exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 4257696543602770772646001 g4257696543602770772646001 57679 g57679 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1307 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1319
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1319 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := S7 257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 257 ∣ 1 + 1319 ^ 16).trans hd)
      have g43 := S1 43 (by norm_num) (by norm_num) (by decide) 257 g257 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 43 g43 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 257 g257 11 g11 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1321
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1321 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g9791777 := S7 9791777 (by norm_num) (by norm_num) (by decide) ((by norm_num : 9791777 ∣ 1 + 1321 ^ 16).trans hd)
      have g383 := S1 383 (by norm_num) (by norm_num) (by decide) 9791777 g9791777 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 9791777 g9791777 383 g383 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1327
    · exfalso; have hd := D8 he
      have g611380753 := S7 611380753 prime_611380753 (by norm_num) (by decide) ((by norm_num : 611380753 ∣ 1 + 1327 ^ 8).trans hd)
      have g305690377 := S1 305690377 prime_305690377 (by norm_num) (by decide) 611380753 g611380753 (by norm_num)
      have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 305690377 g305690377 (by norm_num)
      have g443 := S1 443 (by norm_num) (by norm_num) (by decide) 305690377 g305690377 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 23 g23 443 g443 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g11532769 := S7 11532769 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11532769 ∣ 1 + 1327 ^ 16).trans hd)
      have g1153277 := S1 1153277 (by norm_num) (by norm_num) (by decide) 11532769 g11532769 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1153277 g1153277 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1361
    · exfalso; have hd := D8 he
      have g1638724289 := S7 1638724289 prime_1638724289 (by norm_num) (by decide) ((by norm_num : 1638724289 ∣ 1 + 1361 ^ 8).trans hd)
      have g7803449 := S1 7803449 (by norm_num) (by norm_num) (by decide) 1638724289 g1638724289 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 7803449 g7803449 (by norm_num)
    · exfalso; have hd := D16 he
      have g291457 := S7 291457 (by norm_num) (by norm_num) (by decide) ((by norm_num : 291457 ∣ 1 + 1361 ^ 16).trans hd)
      have g2389 := S1 2389 (by norm_num) (by norm_num) (by decide) 291457 g291457 (by norm_num)
      have g239 := S1 239 (by norm_num) (by norm_num) (by decide) 2389 g2389 (by norm_num)
      exact absurd (S3 5 (by norm_num) (by norm_num) (by decide) 2389 g2389 239 g239 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1367
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1367 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g2753 := S7 2753 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2753 ∣ 1 + 1367 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2753 g2753 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1373
    · exfalso; have hd := D8 he
      have g1249 := S7 1249 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1249 ∣ 1 + 1373 ^ 8).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 1249 g1249 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1381
    · exfalso; have hd := D8 he
      have g8849 := S7 8849 (by norm_num) (by norm_num) (by decide) ((by norm_num : 8849 ∣ 1 + 1381 ^ 8).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 8849 g8849 (by norm_num)
    · exfalso; have hd := D16 he
      have g25409 := S7 25409 (by norm_num) (by norm_num) (by decide) ((by norm_num : 25409 ∣ 1 + 1381 ^ 16).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 25409 g25409 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1399
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1399 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g5569 := S7 5569 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5569 ∣ 1 + 1399 ^ 16).trans hd)
      have g557 := S1 557 (by norm_num) (by norm_num) (by decide) 5569 g5569 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 557 g557 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1409
    · exfalso; have hd := D8 he
      have g260652952177 := S7 260652952177 prime_260652952177 (by norm_num) (by decide) ((by norm_num : 260652952177 ∣ 1 + 1409 ^ 8).trans hd)
      have g1637 := S1 1637 (by norm_num) (by norm_num) (by decide) 260652952177 g260652952177 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1637 g1637 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1409 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1423
    · exfalso; have hd := D8 he
      have g238369 := S7 238369 (by norm_num) (by norm_num) (by decide) ((by norm_num : 238369 ∣ 1 + 1423 ^ 8).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 238369 g238369 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 1423 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1427
    · exfalso; have hd := D8 he
      have g7875475313 := S7 7875475313 prime_7875475313 (by norm_num) (by decide) ((by norm_num : 7875475313 ∣ 1 + 1427 ^ 8).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 7875475313 g7875475313 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1427 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1429
    · exfalso; have hd := D8 he
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 1429 ^ 8).trans hd)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 113 g113 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 113 g113 5 g5 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g192833 := S7 192833 (by norm_num) (by norm_num) (by decide) ((by norm_num : 192833 ∣ 1 + 1429 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 192833 g192833 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1433
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1433 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g158209 := S7 158209 (by norm_num) (by norm_num) (by decide) ((by norm_num : 158209 ∣ 1 + 1433 ^ 16).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 158209 g158209 (by norm_num)
      have g1217 := S1 1217 (by norm_num) (by norm_num) (by decide) 158209 g158209 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 1217 g1217 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1439
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1439 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1153 := S7 1153 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1153 ∣ 1 + 1439 ^ 16).trans hd)
      have g577 := S1 577 (by norm_num) (by norm_num) (by decide) 1153 g1153 (by norm_num)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1447
    · exfalso; have hd := D8 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 1447 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
    · exfalso; have hd := D16 he
      have g11777 := S7 11777 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11777 ∣ 1 + 1447 ^ 16).trans hd)
      have g151 := S1 151 (by norm_num) (by norm_num) (by decide) 11777 g11777 (by norm_num)
      have g19 := S1 19 (by norm_num) (by norm_num) (by decide) 151 g151 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 19 g19 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 11777 g11777 5 g5 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1451
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1451 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g102433 := S7 102433 (by norm_num) (by norm_num) (by decide) ((by norm_num : 102433 ∣ 1 + 1451 ^ 16).trans hd)
      have g51217 := S1 51217 (by norm_num) (by norm_num) (by decide) 102433 g102433 (by norm_num)
      have g25609 := S1 25609 (by norm_num) (by norm_num) (by decide) 51217 g51217 (by norm_num)
      have g197 := S1 197 (by norm_num) (by norm_num) (by decide) 25609 g25609 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 197 g197 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1453
    · exfalso; have hd := D8 he
      have g319489 := S7 319489 (by norm_num) (by norm_num) (by decide) ((by norm_num : 319489 ∣ 1 + 1453 ^ 8).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 319489 g319489 (by norm_num)
      have g743 := S1 743 (by norm_num) (by norm_num) (by decide) 319489 g319489 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 743 g743 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g2753 := S7 2753 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2753 ∣ 1 + 1453 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2753 g2753 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1459
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1459 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g20897 := S7 20897 (by norm_num) (by norm_num) (by decide) ((by norm_num : 20897 ∣ 1 + 1459 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 20897 g20897 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1471
    · exfalso; have hd := D8 he
      have g401 := S7 401 (by norm_num) (by norm_num) (by decide) ((by norm_num : 401 ∣ 1 + 1471 ^ 8).trans hd)
      have g67 := S1 67 (by norm_num) (by norm_num) (by decide) 401 g401 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := S7 353 (by norm_num) (by norm_num) (by decide) ((by norm_num : 353 ∣ 1 + 1471 ^ 16).trans hd)
      have g59 := S1 59 (by norm_num) (by norm_num) (by decide) 353 g353 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 353 g353 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1481
    · exfalso; have hd := D8 he
      have g1014337 := S7 1014337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1014337 ∣ 1 + 1481 ^ 8).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 1014337 g1014337 (by norm_num)
    · exfalso; have hd := D16 he
      have g1697 := S7 1697 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1697 ∣ 1 + 1481 ^ 16).trans hd)
      have g10433 := S7 10433 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10433 ∣ 1 + 1481 ^ 16).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1697 g1697 10433 g10433 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1483
    · exfalso; have hd := D8 he
      have g607697 := S7 607697 (by norm_num) (by norm_num) (by decide) ((by norm_num : 607697 ∣ 1 + 1483 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 607697 g607697 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1483 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1487
    · exfalso; have hd := D8 he
      have g29526449 := S7 29526449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29526449 ∣ 1 + 1487 ^ 8).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 29526449 g29526449 (by norm_num)
    · exfalso; have hd := D16 he
      have g298058138424872129 := S7 298058138424872129 prime_298058138424872129 (by norm_num) (by decide) ((by norm_num : 298058138424872129 ∣ 1 + 1487 ^ 16).trans hd)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 298058138424872129 g298058138424872129 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 298058138424872129 g298058138424872129 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1489
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1489 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1489 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1493
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1493 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g2273 := S7 2273 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2273 ∣ 1 + 1493 ^ 16).trans hd)
      have g6113 := S7 6113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6113 ∣ 1 + 1493 ^ 16).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 2273 g2273 6113 g6113 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1499
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1499 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g273569 := S7 273569 (by norm_num) (by norm_num) (by decide) ((by norm_num : 273569 ∣ 1 + 1499 ^ 16).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 273569 g273569 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 273569 g273569 11 g11 (by norm_num) (by norm_num)) (by norm_num)

set_option maxHeartbeats 12000000 in
theorem zs_1500 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1500 ≤ z) (hi : z < 1800)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 = 8 → z ∈ ({7} : Finset ℕ)) ∧
    (e % 32 = 16 → z ∈ ({7, 41, 73, 113, 157, 167, 173, 199, 307, 449, 599, 607, 617, 643, 743, 811, 937, 967, 1201,
      1213, 1237, 1249, 1277, 1297, 1373, 1579, 1637, 1667, 1747, 1979, 2011, 2027} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1511
    · exfalso; have hd := D8 he
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 1511 ^ 8).trans hd)
      have g769 := S7 769 (by norm_num) (by norm_num) (by decide) ((by norm_num : 769 ∣ 1 + 1511 ^ 8).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 769 g769 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 113 g113 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g57382225467233 := S7 57382225467233 prime_57382225467233 (by norm_num) (by decide) ((by norm_num : 57382225467233 ∣ 1 + 1511 ^ 16).trans hd)
      have g5167 := S1 5167 (by norm_num) (by norm_num) (by decide) 57382225467233 g57382225467233 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 5167 g5167 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1523
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1523 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g6687521 := S7 6687521 (by norm_num) (by norm_num) (by decide) ((by norm_num : 6687521 ∣ 1 + 1523 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 6687521 g6687521 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1531
    · exfalso; have hd := D8 he
      have g15092859525078825081684721 := S7 15092859525078825081684721 prime_15092859525078825081684721 (by norm_num) (by decide) ((by norm_num : 15092859525078825081684721 ∣ 1 + 1531 ^ 8).trans hd)
      have g1571511860719 := S1 1571511860719 prime_1571511860719 (by norm_num) (by decide) 15092859525078825081684721 g15092859525078825081684721 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 1571511860719 g1571511860719 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g8834689 := S7 8834689 (by norm_num) (by norm_num) (by decide) ((by norm_num : 8834689 ∣ 1 + 1531 ^ 16).trans hd)
      have g28499 := S1 28499 (by norm_num) (by norm_num) (by decide) 8834689 g8834689 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 28499 g28499 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1543
    · exfalso; have hd := D8 he
      have g9041 := S7 9041 (by norm_num) (by norm_num) (by decide) ((by norm_num : 9041 ∣ 1 + 1543 ^ 8).trans hd)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 9041 g9041 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 9041 g9041 11 g11 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g128257 := S7 128257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 128257 ∣ 1 + 1543 ^ 16).trans hd)
      have g4933 := S1 4933 (by norm_num) (by norm_num) (by decide) 128257 g128257 (by norm_num)
      have g2467 := S1 2467 (by norm_num) (by norm_num) (by decide) 4933 g4933 (by norm_num)
      have g617 := S1 617 (by norm_num) (by norm_num) (by decide) 2467 g2467 (by norm_num)
      have g103 := S1 103 (by norm_num) (by norm_num) (by decide) 617 g617 (by norm_num)
      exact absurd (S3 13 (by norm_num) (by norm_num) (by decide) 128257 g128257 103 g103 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1549
    · exfalso; have hd := D8 he
      have g1895057 := S7 1895057 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1895057 ∣ 1 + 1549 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1895057 g1895057 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := S7 353 (by norm_num) (by norm_num) (by decide) ((by norm_num : 353 ∣ 1 + 1549 ^ 16).trans hd)
      have g59 := S1 59 (by norm_num) (by norm_num) (by decide) 353 g353 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 353 g353 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1553
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1553 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g724078920953767035521 := S7 724078920953767035521 prime_724078920953767035521 (by norm_num) (by decide) ((by norm_num : 724078920953767035521 ∣ 1 + 1553 ^ 16).trans hd)
      have g156707 := S1 156707 (by norm_num) (by norm_num) (by decide) 724078920953767035521 g724078920953767035521 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 156707 g156707 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1559
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1559 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := S7 257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 257 ∣ 1 + 1559 ^ 16).trans hd)
      have g43 := S1 43 (by norm_num) (by norm_num) (by decide) 257 g257 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 43 g43 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 257 g257 11 g11 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1567
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1567 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g33601 := S7 33601 (by norm_num) (by norm_num) (by decide) ((by norm_num : 33601 ∣ 1 + 1567 ^ 16).trans hd)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 33601 g33601 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1571
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1571 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1571 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1579
    · exfalso; have hd := D8 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1579 ^ 8).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1583
    · exfalso; have hd := D8 he
      have g97154822801 := S7 97154822801 prime_97154822801 (by norm_num) (by decide) ((by norm_num : 97154822801 ∣ 1 + 1583 ^ 8).trans hd)
      have g167 := S1 167 (by norm_num) (by norm_num) (by decide) 97154822801 g97154822801 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 97154822801 g97154822801 167 g167 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g3329 := S7 3329 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3329 ∣ 1 + 1583 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 3329 g3329 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1597
    · exfalso; have hd := D8 he
      have g157489 := S7 157489 (by norm_num) (by norm_num) (by decide) ((by norm_num : 157489 ∣ 1 + 1597 ^ 8).trans hd)
      have g15749 := S1 15749 (by norm_num) (by norm_num) (by decide) 157489 g157489 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 15749 g15749 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1597 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1601
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1601 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g3617 := S7 3617 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3617 ∣ 1 + 1601 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 3617 g3617 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1607
    · exfalso; have hd := D8 he
      have g65393 := S7 65393 (by norm_num) (by norm_num) (by decide) ((by norm_num : 65393 ∣ 1 + 1607 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 65393 g65393 (by norm_num)
    · exfalso; have hd := D16 he
      have g18219137 := S7 18219137 (by norm_num) (by norm_num) (by decide) ((by norm_num : 18219137 ∣ 1 + 1607 ^ 16).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 18219137 g18219137 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1609
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1609 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1217 := S7 1217 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1217 ∣ 1 + 1609 ^ 16).trans hd)
      have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 1217 g1217 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 1217 g1217 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1613
    · exfalso; have hd := D8 he
      have g3137 := S7 3137 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3137 ∣ 1 + 1613 ^ 8).trans hd)
      have g523 := S1 523 (by norm_num) (by norm_num) (by decide) 3137 g3137 (by norm_num)
      have g131 := S1 131 (by norm_num) (by norm_num) (by decide) 523 g523 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 3137 g3137 131 g131 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g15649 := S7 15649 (by norm_num) (by norm_num) (by decide) ((by norm_num : 15649 ∣ 1 + 1613 ^ 16).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 15649 g15649 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1619
    · exfalso; have hd := D8 he
      have g78593 := S7 78593 (by norm_num) (by norm_num) (by decide) ((by norm_num : 78593 ∣ 1 + 1619 ^ 8).trans hd)
      have g13099 := S1 13099 (by norm_num) (by norm_num) (by decide) 78593 g78593 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 13099 g13099 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1619 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1621
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1621 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1621 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1627
    · exfalso; have hd := D8 he
      have g1140353 := S7 1140353 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1140353 ∣ 1 + 1627 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1140353 g1140353 (by norm_num)
    · exfalso; have hd := D16 he
      have g11681 := S7 11681 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11681 ∣ 1 + 1627 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 11681 g11681 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1637
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1637 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1657
    · exfalso; have hd := D8 he
      have g593 := S7 593 (by norm_num) (by norm_num) (by decide) ((by norm_num : 593 ∣ 1 + 1657 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 593 g593 (by norm_num)
    · exfalso; have hd := D16 he
      have g10648513 := S7 10648513 (by norm_num) (by norm_num) (by decide) ((by norm_num : 10648513 ∣ 1 + 1657 ^ 16).trans hd)
      have g5324257 := S1 5324257 (by norm_num) (by norm_num) (by decide) 10648513 g10648513 (by norm_num)
      have g2662129 := S1 2662129 (by norm_num) (by norm_num) (by decide) 5324257 g5324257 (by norm_num)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 2662129 g2662129 (by norm_num)
      have g41 := S1 41 (by norm_num) (by norm_num) (by decide) 2662129 g2662129 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1663
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1663 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := S7 257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 257 ∣ 1 + 1663 ^ 16).trans hd)
      have g2273 := S7 2273 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2273 ∣ 1 + 1663 ^ 16).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 257 g257 2273 g2273 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1667
    · exfalso; have hd := D8 he
      exact SQ 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 * 97 ∣ 1 + 1667 ^ 8).trans hd)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1669
    · exfalso; have hd := D8 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 1669 ^ 8).trans hd)
    · exfalso; have hd := D16 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 1669 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1693
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1693 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g14003094817 := S7 14003094817 prime_14003094817 (by norm_num) (by decide) ((by norm_num : 14003094817 ∣ 1 + 1693 ^ 16).trans hd)
      have g43597 := S1 43597 (by norm_num) (by norm_num) (by decide) 14003094817 g14003094817 (by norm_num)
      have g21799 := S1 21799 (by norm_num) (by norm_num) (by decide) 43597 g43597 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 21799 g21799 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1697
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1697 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 1697 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1699
    · exfalso; have hd := D8 he
      have g34714989264498225976453201 := S7 34714989264498225976453201 prime_34714989264498225976453201 (by norm_num) (by decide) ((by norm_num : 34714989264498225976453201 ∣ 1 + 1699 ^ 8).trans hd)
      have g67 := S1 67 (by norm_num) (by norm_num) (by decide) 34714989264498225976453201 g34714989264498225976453201 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g2753 := S7 2753 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2753 ∣ 1 + 1699 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 2753 g2753 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1709
    · exfalso; have hd := D8 he
      have g39064015937 := S7 39064015937 prime_39064015937 (by norm_num) (by decide) ((by norm_num : 39064015937 ∣ 1 + 1709 ^ 8).trans hd)
      have g1331153 := S1 1331153 (by norm_num) (by norm_num) (by decide) 39064015937 g39064015937 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1331153 g1331153 (by norm_num)
    · exfalso; have hd := D16 he
      have g13099841 := S7 13099841 (by norm_num) (by norm_num) (by decide) ((by norm_num : 13099841 ∣ 1 + 1709 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 13099841 g13099841 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1721
    · exfalso; have hd := D8 he
      have g1303073 := S7 1303073 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1303073 ∣ 1 + 1721 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1303073 g1303073 (by norm_num)
    · exfalso; have hd := D16 he
      have g3481187233 := S7 3481187233 prime_3481187233 (by norm_num) (by decide) ((by norm_num : 3481187233 ∣ 1 + 1721 ^ 16).trans hd)
      have g4691627 := S1 4691627 (by norm_num) (by norm_num) (by decide) 3481187233 g3481187233 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 4691627 g4691627 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1723
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1723 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 1723 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1733
    · exfalso; have hd := D8 he
      have g1697 := S7 1697 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1697 ∣ 1 + 1733 ^ 8).trans hd)
      have g283 := S1 283 (by norm_num) (by norm_num) (by decide) 1697 g1697 (by norm_num)
      have g71 := S1 71 (by norm_num) (by norm_num) (by decide) 283 g283 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)
    · exfalso; have hd := D16 he
      have g11910497 := S7 11910497 (by norm_num) (by norm_num) (by decide) ((by norm_num : 11910497 ∣ 1 + 1733 ^ 16).trans hd)
      have g4481 := S1 4481 (by norm_num) (by norm_num) (by decide) 11910497 g11910497 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 4481 g4481 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1741
    · exfalso; have hd := D8 he
      have g16433 := S7 16433 (by norm_num) (by norm_num) (by decide) ((by norm_num : 16433 ∣ 1 + 1741 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 16433 g16433 (by norm_num)
    · exfalso; have hd := D16 he
      have g5554433 := S7 5554433 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5554433 ∣ 1 + 1741 ^ 16).trans hd)
      have g337 := S1 337 (by norm_num) (by norm_num) (by decide) 5554433 g5554433 (by norm_num)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1747
    · exfalso; have hd := D8 he
      have g5994449 := S7 5994449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 5994449 ∣ 1 + 1747 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 5994449 g5994449 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1753
    · exfalso; have hd := D8 he
      have g44588753651715539427437281 := S7 44588753651715539427437281 prime_44588753651715539427437281 (by norm_num) (by decide) ((by norm_num : 44588753651715539427437281 ∣ 1 + 1753 ^ 8).trans hd)
      have g199 := S1 199 (by norm_num) (by norm_num) (by decide) 44588753651715539427437281 g44588753651715539427437281 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 199 g199 (by norm_num)
    · exfalso; have hd := D16 he
      have g817889 := S7 817889 (by norm_num) (by norm_num) (by decide) ((by norm_num : 817889 ∣ 1 + 1753 ^ 16).trans hd)
      have g199 := S1 199 (by norm_num) (by norm_num) (by decide) 817889 g817889 (by norm_num)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 199 g199 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1759
    · exfalso; have hd := D8 he
      have g45953 := S7 45953 (by norm_num) (by norm_num) (by decide) ((by norm_num : 45953 ∣ 1 + 1759 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 45953 g45953 (by norm_num)
    · exfalso; have hd := D16 he
      have g378593 := S7 378593 (by norm_num) (by norm_num) (by decide) ((by norm_num : 378593 ∣ 1 + 1759 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 378593 g378593 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1777
    · exfalso; have hd := D8 he
      have g49712937585586541809314241 := S7 49712937585586541809314241 prime_49712937585586541809314241 (by norm_num) (by decide) ((by norm_num : 49712937585586541809314241 ∣ 1 + 1777 ^ 8).trans hd)
      have g94219 := S1 94219 (by norm_num) (by norm_num) (by decide) 49712937585586541809314241 g49712937585586541809314241 (by norm_num)
      have g673 := S1 673 (by norm_num) (by norm_num) (by decide) 94219 g94219 (by norm_num)
      have g337 := S1 337 (by norm_num) (by norm_num) (by decide) 673 g673 (by norm_num)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · exfalso; have hd := D16 he
      have g16001 := S7 16001 (by norm_num) (by norm_num) (by decide) ((by norm_num : 16001 ∣ 1 + 1777 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 16001 g16001 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1783
    · exfalso; have hd := D8 he
      have g375233 := S7 375233 (by norm_num) (by norm_num) (by decide) ((by norm_num : 375233 ∣ 1 + 1783 ^ 8).trans hd)
      have g62539 := S1 62539 (by norm_num) (by norm_num) (by decide) 375233 g375233 (by norm_num)
      have g53 := S1 53 (by norm_num) (by norm_num) (by decide) 62539 g62539 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 53 g53 (by norm_num)
    · exfalso; have hd := D16 he
      have g40961 := S7 40961 (by norm_num) (by norm_num) (by decide) ((by norm_num : 40961 ∣ 1 + 1783 ^ 16).trans hd)
      have g6827 := S1 6827 (by norm_num) (by norm_num) (by decide) 40961 g40961 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 40961 g40961 6827 g6827 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1787
    · exfalso; have hd := D8 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 1787 ^ 8).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g2081 := S7 2081 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2081 ∣ 1 + 1787 ^ 16).trans hd)
      have g347 := S1 347 (by norm_num) (by norm_num) (by decide) 2081 g2081 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 2081 g2081 347 g347 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1789
    · exfalso; have hd := D8 he
      have g3452552017 := S7 3452552017 prime_3452552017 (by norm_num) (by decide) ((by norm_num : 3452552017 ∣ 1 + 1789 ^ 8).trans hd)
      have g1726276009 := S1 1726276009 prime_1726276009 (by norm_num) (by decide) 3452552017 g3452552017 (by norm_num)
      have g8663 := S1 8663 (by norm_num) (by norm_num) (by decide) 1726276009 g1726276009 (by norm_num)
      exact S6 19 (by norm_num) (by norm_num) (by decide) 8663 g8663 (by norm_num)
    · exfalso; have hd := D16 he
      have g769 := S7 769 (by norm_num) (by norm_num) (by decide) ((by norm_num : 769 ∣ 1 + 1789 ^ 16).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 769 g769 (by norm_num)
      have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 769 g769 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 11 g11 (by norm_num) (by norm_num)) (by norm_num)

set_option maxHeartbeats 12000000 in
theorem zs_1800 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1800 ≤ z) (hi : z < 2100)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 = 8 → z ∈ ({7} : Finset ℕ)) ∧
    (e % 32 = 16 → z ∈ ({7, 41, 73, 113, 157, 167, 173, 199, 307, 449, 599, 607, 617, 643, 743, 811, 937, 967, 1201,
      1213, 1237, 1249, 1277, 1297, 1373, 1579, 1637, 1667, 1747, 1979, 2011, 2027} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have SQ : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({z} : Finset ℕ) → c * c ∣ 1 + z ^ e → False :=
    fun c hc hc2 hcz h => S_sq hP (prime_dvd_prime_pow hz) E hc hc2 hcz ((h.mul_left _).mul_right _)
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1801
    · exfalso; have hd := D8 he
      have g174929 := S7 174929 (by norm_num) (by norm_num) (by decide) ((by norm_num : 174929 ∣ 1 + 1801 ^ 8).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 174929 g174929 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1801 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1811
    · exfalso; have hd := D8 he
      have g1861745233 := S7 1861745233 prime_1861745233 (by norm_num) (by decide) ((by norm_num : 1861745233 ∣ 1 + 1811 ^ 8).trans hd)
      have g269 := S1 269 (by norm_num) (by norm_num) (by decide) 1861745233 g1861745233 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 269 g269 (by norm_num)
    · exfalso; have hd := D16 he
      have g3475883681 := S7 3475883681 prime_3475883681 (by norm_num) (by decide) ((by norm_num : 3475883681 ∣ 1 + 1811 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 3475883681 g3475883681 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1823
    · exfalso; have hd := D8 he
      have g641 := S7 641 (by norm_num) (by norm_num) (by decide) ((by norm_num : 641 ∣ 1 + 1823 ^ 8).trans hd)
      have g107 := S1 107 (by norm_num) (by norm_num) (by decide) 641 g641 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1823 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1831
    · exfalso; have hd := D8 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 1831 ^ 8).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · exfalso; have hd := D16 he
      have g1012321 := S7 1012321 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1012321 ∣ 1 + 1831 ^ 16).trans hd)
      have g373 := S1 373 (by norm_num) (by norm_num) (by decide) 1012321 g1012321 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 373 g373 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1847
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1847 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g4801 := S7 4801 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4801 ∣ 1 + 1847 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 4801 g4801 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1861
    · exfalso; have hd := D8 he
      have g593 := S7 593 (by norm_num) (by norm_num) (by decide) ((by norm_num : 593 ∣ 1 + 1861 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 593 g593 (by norm_num)
    · exfalso; have hd := D16 he
      have g95873 := S7 95873 (by norm_num) (by norm_num) (by decide) ((by norm_num : 95873 ∣ 1 + 1861 ^ 16).trans hd)
      exact S6 29 (by norm_num) (by norm_num) (by decide) 95873 g95873 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1867
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1867 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1153 := S7 1153 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1153 ∣ 1 + 1867 ^ 16).trans hd)
      have g577 := S1 577 (by norm_num) (by norm_num) (by decide) 1153 g1153 (by norm_num)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1871
    · exfalso; have hd := D8 he
      have g75086230851720457458598081 := S7 75086230851720457458598081 prime_75086230851720457458598081 (by norm_num) (by decide) ((by norm_num : 75086230851720457458598081 ∣ 1 + 1871 ^ 8).trans hd)
      have g373 := S1 373 (by norm_num) (by norm_num) (by decide) 75086230851720457458598081 g75086230851720457458598081 (by norm_num)
      have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 373 g373 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1871 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1873
    · exfalso; have hd := D8 he
      have g18049 := S7 18049 (by norm_num) (by norm_num) (by decide) ((by norm_num : 18049 ∣ 1 + 1873 ^ 8).trans hd)
      exact S6 19 (by norm_num) (by norm_num) (by decide) 18049 g18049 (by norm_num)
    · exfalso; have hd := D16 he
      exact SQ 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 * 97 ∣ 1 + 1873 ^ 16).trans hd)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1877
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1877 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1877 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1879
    · exfalso; have hd := D8 he
      have g113 := S7 113 (by norm_num) (by norm_num) (by decide) ((by norm_num : 113 ∣ 1 + 1879 ^ 8).trans hd)
      have g1553 := S7 1553 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1553 ∣ 1 + 1879 ^ 8).trans hd)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 113 g113 1553 g1553 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g1070369 := S7 1070369 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1070369 ∣ 1 + 1879 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1070369 g1070369 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1889
    · exfalso; have hd := D8 he
      have g4219217 := S7 4219217 (by norm_num) (by norm_num) (by decide) ((by norm_num : 4219217 ∣ 1 + 1889 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 4219217 g4219217 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1889 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1901
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1901 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g39041 := S7 39041 (by norm_num) (by norm_num) (by decide) ((by norm_num : 39041 ∣ 1 + 1901 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 39041 g39041 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1907
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1907 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 1907 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1913
    · exfalso; have hd := D8 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 1913 ^ 8).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g2299937 := S7 2299937 (by norm_num) (by norm_num) (by decide) ((by norm_num : 2299937 ∣ 1 + 1913 ^ 16).trans hd)
      have g89 := S1 89 (by norm_num) (by norm_num) (by decide) 2299937 g2299937 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1931
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1931 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g40577 := S7 40577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 40577 ∣ 1 + 1931 ^ 16).trans hd)
      have g6763 := S1 6763 (by norm_num) (by norm_num) (by decide) 40577 g40577 (by norm_num)
      have g89 := S1 89 (by norm_num) (by norm_num) (by decide) 6763 g6763 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 89 g89 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1933
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1933 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g641 := S7 641 (by norm_num) (by norm_num) (by decide) ((by norm_num : 641 ∣ 1 + 1933 ^ 16).trans hd)
      have g107 := S1 107 (by norm_num) (by norm_num) (by decide) 641 g641 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1949
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1949 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g583937 := S7 583937 (by norm_num) (by norm_num) (by decide) ((by norm_num : 583937 ∣ 1 + 1949 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 583937 g583937 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1951
    · exfalso; have hd := D8 he
      have g9601 := S7 9601 (by norm_num) (by norm_num) (by decide) ((by norm_num : 9601 ∣ 1 + 1951 ^ 8).trans hd)
      have g4801 := S1 4801 (by norm_num) (by norm_num) (by decide) 9601 g9601 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 4801 g4801 (by norm_num)
    · exfalso; have hd := D16 he
      have g44449 := S7 44449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 44449 ∣ 1 + 1951 ^ 16).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 44449 g44449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1973
    · exfalso; have hd := D8 he
      have g3855409 := S7 3855409 (by norm_num) (by norm_num) (by decide) ((by norm_num : 3855409 ∣ 1 + 1973 ^ 8).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 3855409 g3855409 (by norm_num)
      have g47 := S1 47 (by norm_num) (by norm_num) (by decide) 3855409 g3855409 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5 g5 47 g47 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g44585571617 := S7 44585571617 prime_44585571617 (by norm_num) (by decide) ((by norm_num : 44585571617 ∣ 1 + 1973 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 44585571617 g44585571617 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1979
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1979 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1987
    · exfalso; have hd := D8 he
      have g262198292243137 := S7 262198292243137 prime_262198292243137 (by norm_num) (by decide) ((by norm_num : 262198292243137 ∣ 1 + 1987 ^ 8).trans hd)
      have g21383 := S1 21383 (by norm_num) (by norm_num) (by decide) 262198292243137 g262198292243137 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 21383 g21383 (by norm_num)
    · exfalso; have hd := D16 he
      have g641 := S7 641 (by norm_num) (by norm_num) (by decide) ((by norm_num : 641 ∣ 1 + 1987 ^ 16).trans hd)
      have g107 := S1 107 (by norm_num) (by norm_num) (by decide) 641 g641 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1993
    · exfalso; have hd := D8 he
      have g31917217 := S7 31917217 (by norm_num) (by norm_num) (by decide) ((by norm_num : 31917217 ∣ 1 + 1993 ^ 8).trans hd)
      have g4751 := S1 4751 (by norm_num) (by norm_num) (by decide) 31917217 g31917217 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 4751 g4751 (by norm_num)
    · exfalso; have hd := D16 he
      have g29537 := S7 29537 (by norm_num) (by norm_num) (by decide) ((by norm_num : 29537 ∣ 1 + 1993 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 29537 g29537 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1997
    · exfalso; have hd := D8 he
      have g292083232917564916412257 := S7 292083232917564916412257 prime_292083232917564916412257 (by norm_num) (by decide) ((by norm_num : 292083232917564916412257 ∣ 1 + 1997 ^ 8).trans hd)
      have g214736371 := S1 214736371 prime_214736371 (by norm_num) (by decide) 292083232917564916412257 g292083232917564916412257 (by norm_num)
      have g2334091 := S1 2334091 (by norm_num) (by norm_num) (by decide) 214736371 g214736371 (by norm_num)
      have g583523 := S1 583523 (by norm_num) (by norm_num) (by decide) 2334091 g2334091 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 583523 g583523 (by norm_num)
    · exfalso; have hd := D16 he
      have g15649 := S7 15649 (by norm_num) (by norm_num) (by decide) ((by norm_num : 15649 ∣ 1 + 1997 ^ 16).trans hd)
      exact S6 5 (by norm_num) (by norm_num) (by decide) 15649 g15649 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 1999
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 1999 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g16001 := S7 16001 (by norm_num) (by norm_num) (by decide) ((by norm_num : 16001 ∣ 1 + 1999 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 16001 g16001 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2003
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 2003 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g341729 := S7 341729 (by norm_num) (by norm_num) (by decide) ((by norm_num : 341729 ∣ 1 + 2003 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 341729 g341729 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2011
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 2011 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2017
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 2017 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g449 := S7 449 (by norm_num) (by norm_num) (by decide) ((by norm_num : 449 ∣ 1 + 2017 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2027
    · exfalso; have hd := D8 he
      have g673 := S7 673 (by norm_num) (by norm_num) (by decide) ((by norm_num : 673 ∣ 1 + 2027 ^ 8).trans hd)
      have g337 := S1 337 (by norm_num) (by norm_num) (by decide) 673 g673 (by norm_num)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · simp
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2029
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 2029 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g90977 := S7 90977 (by norm_num) (by norm_num) (by decide) ((by norm_num : 90977 ∣ 1 + 2029 ^ 16).trans hd)
      have g257 := S1 257 (by norm_num) (by norm_num) (by decide) 90977 g90977 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 90977 g90977 257 g257 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2039
    · exfalso; have hd := D8 he
      have g241 := S7 241 (by norm_num) (by norm_num) (by decide) ((by norm_num : 241 ∣ 1 + 2039 ^ 8).trans hd)
      exact S6 11 (by norm_num) (by norm_num) (by decide) 241 g241 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := S7 257 (by norm_num) (by norm_num) (by decide) ((by norm_num : 257 ∣ 1 + 2039 ^ 16).trans hd)
      have g1041889 := S7 1041889 (by norm_num) (by norm_num) (by decide) ((by norm_num : 1041889 ∣ 1 + 2039 ^ 16).trans hd)
      exact absurd (S3 43 (by norm_num) (by norm_num) (by decide) 257 g257 1041889 g1041889 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2053
    · exfalso; have hd := D8 he
      have g157790771387783474187901681 := S7 157790771387783474187901681 prime_157790771387783474187901681 (by norm_num) (by decide) ((by norm_num : 157790771387783474187901681 ∣ 1 + 2053 ^ 8).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 157790771387783474187901681 g157790771387783474187901681 (by norm_num)
    · exfalso; have hd := D16 he
      have g100769 := S7 100769 (by norm_num) (by norm_num) (by decide) ((by norm_num : 100769 ∣ 1 + 2053 ^ 16).trans hd)
      have g3359 := S1 3359 (by norm_num) (by norm_num) (by decide) 100769 g100769 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 100769 g100769 3359 g3359 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2063
    · exfalso; have hd := D8 he
      exact SQ 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 * 17 ∣ 1 + 2063 ^ 8).trans hd)
    · exfalso; have hd := D16 he
      have g902753 := S7 902753 (by norm_num) (by norm_num) (by decide) ((by norm_num : 902753 ∣ 1 + 2063 ^ 16).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 902753 g902753 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2069
    · exfalso; have hd := D8 he
      have g17 := S7 17 (by norm_num) (by norm_num) (by decide) ((by norm_num : 17 ∣ 1 + 2069 ^ 8).trans hd)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g5542095809 := S7 5542095809 prime_5542095809 (by norm_num) (by decide) ((by norm_num : 5542095809 ∣ 1 + 2069 ^ 16).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 5542095809 g5542095809 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 5542095809 g5542095809 5 g5 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2081
    · exfalso; have hd := D8 he
      have g337 := S7 337 (by norm_num) (by norm_num) (by decide) ((by norm_num : 337 ∣ 1 + 2081 ^ 8).trans hd)
      exact S6 13 (by norm_num) (by norm_num) (by decide) 337 g337 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := S7 193 (by norm_num) (by norm_num) (by decide) ((by norm_num : 193 ∣ 1 + 2081 ^ 16).trans hd)
      have g97 := S1 97 (by norm_num) (by norm_num) (by decide) 193 g193 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2083
    · exfalso; have hd := D8 he
      have g177208342683739494697085521 := S7 177208342683739494697085521 prime_177208342683739494697085521 (by norm_num) (by decide) ((by norm_num : 177208342683739494697085521 ∣ 1 + 2083 ^ 8).trans hd)
      have g14102207757738301344667 := S1 14102207757738301344667 prime_14102207757738301344667 (by norm_num) (by decide) 177208342683739494697085521 g177208342683739494697085521 (by norm_num)
      have g439631 := S1 439631 (by norm_num) (by norm_num) (by decide) 14102207757738301344667 g14102207757738301344667 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 439631 g439631 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 2083 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2087
    · exfalso; have hd := D8 he
      have g365656673 := S7 365656673 prime_365656673 (by norm_num) (by decide) ((by norm_num : 365656673 ∣ 1 + 2087 ^ 8).trans hd)
      have g1061 := S1 1061 (by norm_num) (by norm_num) (by decide) 365656673 g365656673 (by norm_num)
      exact S6 3 (by norm_num) (by norm_num) (by decide) 1061 g1061 (by norm_num)
    · exfalso; have hd := D16 he
      have g36853030570720289 := S7 36853030570720289 prime_36853030570720289 (by norm_num) (by decide) ((by norm_num : 36853030570720289 ∣ 1 + 2087 ^ 16).trans hd)
      have g5 := S1 5 (by norm_num) (by norm_num) (by decide) 36853030570720289 g36853030570720289 (by norm_num)
      exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 36853030570720289 g36853030570720289 5 g5 (by norm_num) (by norm_num)) (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2089
    · exfalso; have hd := D8 he
      have g53377 := S7 53377 (by norm_num) (by norm_num) (by decide) ((by norm_num : 53377 ∣ 1 + 2089 ^ 8).trans hd)
      have g2053 := S1 2053 (by norm_num) (by norm_num) (by decide) 53377 g53377 (by norm_num)
      exact absurd (S3 13 (by norm_num) (by norm_num) (by decide) 53377 g53377 2053 g2053 (by norm_num) (by norm_num)) (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := S7 97 (by norm_num) (by norm_num) (by decide) ((by norm_num : 97 ∣ 1 + 2089 ^ 16).trans hd)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_⟩  -- z = 2099
    · exfalso; have hd := D8 he
      have g735073 := S7 735073 (by norm_num) (by norm_num) (by decide) ((by norm_num : 735073 ∣ 1 + 2099 ^ 8).trans hd)
      have g2341 := S1 2341 (by norm_num) (by norm_num) (by decide) 735073 g735073 (by norm_num)
      have g1171 := S1 1171 (by norm_num) (by norm_num) (by decide) 2341 g2341 (by norm_num)
      have g293 := S1 293 (by norm_num) (by norm_num) (by decide) 1171 g1171 (by norm_num)
      exact S6 7 (by norm_num) (by norm_num) (by decide) 293 g293 (by norm_num)
    · exfalso; have hd := D16 he
      have g577 := S7 577 (by norm_num) (by norm_num) (by decide) ((by norm_num : 577 ∣ 1 + 2099 ^ 16).trans hd)
      exact S6 17 (by norm_num) (by norm_num) (by decide) 577 g577 (by norm_num)

-- The sieve of z.
theorem zsieve {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 7 ≤ z) (hi : z < 2100)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 = 8 → z ∈ ({7} : Finset ℕ)) ∧
    (e % 32 = 16 → z ∈ ({7, 41, 73, 113, 157, 167, 173, 199, 307, 449, 599, 607, 617, 643, 743, 811, 937, 967, 1201,
      1213, 1237, 1249, 1277, 1297, 1373, 1579, 1637, 1667, 1747, 1979, 2011, 2027} : Finset ℕ)) := by
  rcases Nat.lt_or_ge z 300 with h | h
  · exact zs_0 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 600 with h | h
  · exact zs_300 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 900 with h | h
  · exact zs_600 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1200 with h | h
  · exact zs_900 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1500 with h | h
  · exact zs_1200 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1800 with h | h
  · exact zs_1500 hP hz (by omega) h E
  exact zs_1800 hP hz (by omega) hi E

-- Section 2. The step.
theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1.H4 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max A1 A2, fun n h z hz lo hi hS c h7 c0 c1 c2 c4 c5 c6 c7 c15 U R => ?_⟩
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hz2 : z ≠ 2 := by omega
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  obtain ⟨z8, z16⟩ := zsieve hP hz lo hi E
  have hc : n.factorization z % 16 = 8 ∨ n.factorization z % 32 = 16 ∨ n.factorization z % 32 = 0 := by omega
  rcases hc with c' | c' | c'
  · exfalso
    have hm := z8 c'
    rw [Finset.mem_singleton] at hm
    subst hm
    exact (h7 rfl).2 8 (by simp) c'
  · have hm := z16 c'
    have hz7 : z ≠ 7 := by
      rintro rfl
      exact (h7 rfl).2 16 (by simp) c'
    rw [Finset.mem_insert] at hm
    exact (h1 n h z hz hS c' (hm.resolve_left hz7) c0 c1 c2 c4 c5 c6 c7 c15 U R).trans
      (le_max_left _ _)
  · exact (h2 n h z hz lo hi hS c' h7 c0 c1 c2 c4 c5 c6 c7 c15 U R).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1
