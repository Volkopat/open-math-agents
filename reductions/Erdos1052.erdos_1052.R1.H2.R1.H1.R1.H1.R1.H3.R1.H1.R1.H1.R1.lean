import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1.H1.R1
-- Credit: @adammcarter
-- Splits step H1 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1 (3 the only repeated odd
-- prime, exponent e of 3 above 800) by new classes of a = padicValNat 2 n that are excluded for EVERY
-- such exponent, and further classes excluded when e is 2 mod 4.  Proving the two H proves the step.
--
-- PROVED BELOW (uniform in e):
--   For each of the 54 values d of the third set in H1/H2 (31 <= d <= 200), a is no odd multiple of d
--   (kill2_1_d): then 2^d + 1 divides 2^a + 1, every odd prime of 2^d + 1 is a simple prime of n with
--   source 2^a + 1, and the odd primes of p + 1 for a simple prime p are again simple primes; the
--   chains give an odd prime with two sources or a square in the balance equation
--   (2^a + 1)(3^e + 1) prod (p + 1) = 2^(a+1) 3^e prod p.
--   If e is 2 mod 4, then 5 divides 3^e + 1 (3^2 + 1 = 10) and is a simple prime with that source;
--   with it, a is also no odd multiple of the 15 values of the fourth set in H1 (kill2_2_d),
--   among them 2, so a is not 2 mod 4.
-- Witness primes above 4.3 * 10^7 are certified by the Lucas test.
--
-- H1 (OPEN): e > 800, e = 2 mod 4, with all the classes listed.
-- H2 (OPEN): e > 800, e not 2 mod 4, with all the classes listed.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1 hiding H1 H2 main

-- H1: a is bounded over the unitary perfect numbers whose only repeated odd prime is 3, with exponent
-- e of 3 above 800 and e = 2 mod 4, e no odd multiple of the first set, and a no odd multiple of any d
-- in the second (DA), third or fourth set.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < n.factorization 3 →
    n.factorization 3 % 4 = 2 →
    (∀ d ∈ ({502, 503, 508, 509, 512, 514, 521, 523, 524, 526, 538, 541, 542, 547, 548, 554, 556, 557,
        562, 563, 566, 569, 571, 586, 587, 593, 596, 599, 601, 604, 607, 613, 614, 617, 619,
        622, 626, 628, 631, 634, 641, 643, 647, 652, 653, 659, 661, 662, 668, 673, 674, 677,
        683, 691, 692, 694, 698, 701, 706, 709, 716, 718, 719, 724, 727, 733, 734, 739, 743,
        746, 751, 757, 758, 761, 766, 769, 772, 773, 778, 787, 788, 794, 796, 797} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({31, 40, 41, 43, 44, 47, 49, 53, 58, 61, 71, 73, 79, 88, 89, 92, 93, 101, 103, 104, 107, 109,
        113, 127, 128, 129, 136, 137, 139, 148, 151, 159, 161, 163, 164, 166, 167, 172, 173,
        174, 176, 178, 179, 181, 183, 184, 187, 188, 191, 193, 194, 197, 199, 200} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({2, 6, 9, 11, 13, 21, 23, 158, 169, 219, 272, 302, 332, 356, 373} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H2: the same with e not 2 mod 4, and a no odd multiple of any d in the second (DA) or third set.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < n.factorization 3 →
    n.factorization 3 % 4 ≠ 2 →
    (∀ d ∈ ({502, 503, 508, 509, 512, 514, 521, 523, 524, 526, 538, 541, 542, 547, 548, 554, 556, 557,
        562, 563, 566, 569, 571, 586, 587, 593, 596, 599, 601, 604, 607, 613, 614, 617, 619,
        622, 626, 628, 631, 634, 641, 643, 647, 652, 653, 659, 661, 662, 668, 673, 674, 677,
        683, 691, 692, 694, 698, 701, 706, 709, 716, 718, 719, 724, 727, 733, 734, 739, 743,
        746, 751, 757, 758, 761, 766, 769, 772, 773, 778, 787, 788, 794, 796, 797} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({31, 40, 41, 43, 44, 47, 49, 53, 58, 61, 71, 73, 79, 88, 89, 92, 93, 101, 103, 104, 107, 109,
        113, 127, 128, 129, 136, 137, 139, 148, 151, 159, 161, 163, 164, 166, 167, 172, 173,
        174, 176, 178, 179, 181, 183, 184, 187, 188, 191, 193, 194, 197, 199, 200} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
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

theorem prime_119782433 : Nat.Prime 119782433 := by
  refine lucas_primality 119782433 (3 : ZMod 119782433) ?_ (fun q hq hd => ?_)
  · rw [show 119782433 - 1 = 119782432 from by norm_num]
    reduce_mod_char
  · have e : 119782433 - 1 = [2 ^ 5, 7 ^ 1, 11 ^ 1, 173 ^ 1, 281 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119782433 - 1) / 2 = 59891216 from by norm_num]
      have h2 : (3 : ZMod 119782433) ^ 59891216 = ((119782432 : ℕ) : ZMod 119782433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119782433 - 1) / 7 = 17111776 from by norm_num]
      have h2 : (3 : ZMod 119782433) ^ 17111776 = ((56875368 : ℕ) : ZMod 119782433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119782433 - 1) / 11 = 10889312 from by norm_num]
      have h2 : (3 : ZMod 119782433) ^ 10889312 = ((65536 : ℕ) : ZMod 119782433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119782433 - 1) / 173 = 692384 from by norm_num]
      have h2 : (3 : ZMod 119782433) ^ 692384 = ((80376334 : ℕ) : ZMod 119782433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119782433 - 1) / 281 = 426272 from by norm_num]
      have h2 : (3 : ZMod 119782433) ^ 426272 = ((62191364 : ℕ) : ZMod 119782433) := by
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

theorem prime_529510939 : Nat.Prime 529510939 := by
  refine lucas_primality 529510939 (3 : ZMod 529510939) ?_ (fun q hq hd => ?_)
  · rw [show 529510939 - 1 = 529510938 from by norm_num]
    reduce_mod_char
  · have e : 529510939 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 31 ^ 1, 258803 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (529510939 - 1) / 2 = 264755469 from by norm_num]
      have h2 : (3 : ZMod 529510939) ^ 264755469 = ((529510938 : ℕ) : ZMod 529510939) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (529510939 - 1) / 3 = 176503646 from by norm_num]
      have h2 : (3 : ZMod 529510939) ^ 176503646 = ((500071047 : ℕ) : ZMod 529510939) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (529510939 - 1) / 11 = 48137358 from by norm_num]
      have h2 : (3 : ZMod 529510939) ^ 48137358 = ((231667365 : ℕ) : ZMod 529510939) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (529510939 - 1) / 31 = 17080998 from by norm_num]
      have h2 : (3 : ZMod 529510939) ^ 17080998 = ((41274901 : ℕ) : ZMod 529510939) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (529510939 - 1) / 258803 = 2046 from by norm_num]
      have h2 : (3 : ZMod 529510939) ^ 2046 = ((113130690 : ℕ) : ZMod 529510939) := by
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

theorem prime_251906329 : Nat.Prime 251906329 := by
  refine lucas_primality 251906329 (7 : ZMod 251906329) ?_ (fun q hq hd => ?_)
  · rw [show 251906329 - 1 = 251906328 from by norm_num]
    reduce_mod_char
  · have e : 251906329 - 1 = [2 ^ 3, 3 ^ 3, 83 ^ 1, 14051 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (251906329 - 1) / 2 = 125953164 from by norm_num]
      have h2 : (7 : ZMod 251906329) ^ 125953164 = ((251906328 : ℕ) : ZMod 251906329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (251906329 - 1) / 3 = 83968776 from by norm_num]
      have h2 : (7 : ZMod 251906329) ^ 83968776 = ((115205509 : ℕ) : ZMod 251906329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (251906329 - 1) / 83 = 3035016 from by norm_num]
      have h2 : (7 : ZMod 251906329) ^ 3035016 = ((172816262 : ℕ) : ZMod 251906329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (251906329 - 1) / 14051 = 17928 from by norm_num]
      have h2 : (7 : ZMod 251906329) ^ 17928 = ((209470014 : ℕ) : ZMod 251906329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_415141630193 : Nat.Prime 415141630193 := by
  refine lucas_primality 415141630193 (3 : ZMod 415141630193) ?_ (fun q hq hd => ?_)
  · rw [show 415141630193 - 1 = 415141630192 from by norm_num]
    reduce_mod_char
  · have e : 415141630193 - 1 = [2 ^ 4, 103 ^ 1, 251906329 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (415141630193 - 1) / 2 = 207570815096 from by norm_num]
      have h2 : (3 : ZMod 415141630193) ^ 207570815096 = ((415141630192 : ℕ) : ZMod 415141630193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (415141630193 - 1) / 103 = 4030501264 from by norm_num]
      have h2 : (3 : ZMod 415141630193) ^ 4030501264 = ((64 : ℕ) : ZMod 415141630193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_251906329).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (415141630193 - 1) / 251906329 = 1648 from by norm_num]
      have h2 : (3 : ZMod 415141630193) ^ 1648 = ((371407806377 : ℕ) : ZMod 415141630193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_974510869 : Nat.Prime 974510869 := by
  refine lucas_primality 974510869 (2 : ZMod 974510869) ?_ (fun q hq hd => ?_)
  · rw [show 974510869 - 1 = 974510868 from by norm_num]
    reduce_mod_char
  · have e : 974510869 - 1 = [2 ^ 2, 3 ^ 1, 61 ^ 1, 1331299 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (974510869 - 1) / 2 = 487255434 from by norm_num]
      have h2 : (2 : ZMod 974510869) ^ 487255434 = ((974510868 : ℕ) : ZMod 974510869) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (974510869 - 1) / 3 = 324836956 from by norm_num]
      have h2 : (2 : ZMod 974510869) ^ 324836956 = ((912373128 : ℕ) : ZMod 974510869) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (974510869 - 1) / 61 = 15975588 from by norm_num]
      have h2 : (2 : ZMod 974510869) ^ 15975588 = ((363317613 : ℕ) : ZMod 974510869) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (974510869 - 1) / 1331299 = 732 from by norm_num]
      have h2 : (2 : ZMod 974510869) ^ 732 = ((617617794 : ℕ) : ZMod 974510869) := by
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

theorem prime_1591582393 : Nat.Prime 1591582393 := by
  refine lucas_primality 1591582393 (5 : ZMod 1591582393) ?_ (fun q hq hd => ?_)
  · rw [show 1591582393 - 1 = 1591582392 from by norm_num]
    reduce_mod_char
  · have e : 1591582393 - 1 = [2 ^ 3, 3 ^ 3, 43 ^ 1, 349 ^ 1, 491 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1591582393 - 1) / 2 = 795791196 from by norm_num]
      have h2 : (5 : ZMod 1591582393) ^ 795791196 = ((1591582392 : ℕ) : ZMod 1591582393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1591582393 - 1) / 3 = 530527464 from by norm_num]
      have h2 : (5 : ZMod 1591582393) ^ 530527464 = ((1008718489 : ℕ) : ZMod 1591582393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1591582393 - 1) / 43 = 37013544 from by norm_num]
      have h2 : (5 : ZMod 1591582393) ^ 37013544 = ((16777216 : ℕ) : ZMod 1591582393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1591582393 - 1) / 349 = 4560408 from by norm_num]
      have h2 : (5 : ZMod 1591582393) ^ 4560408 = ((518666921 : ℕ) : ZMod 1591582393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1591582393 - 1) / 491 = 3241512 from by norm_num]
      have h2 : (5 : ZMod 1591582393) ^ 3241512 = ((927143389 : ℕ) : ZMod 1591582393) := by
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

theorem prime_105856693 : Nat.Prime 105856693 := by
  refine lucas_primality 105856693 (2 : ZMod 105856693) ?_ (fun q hq hd => ?_)
  · rw [show 105856693 - 1 = 105856692 from by norm_num]
    reduce_mod_char
  · have e : 105856693 - 1 = [2 ^ 2, 3 ^ 1, 31 ^ 1, 284561 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105856693 - 1) / 2 = 52928346 from by norm_num]
      have h2 : (2 : ZMod 105856693) ^ 52928346 = ((105856692 : ℕ) : ZMod 105856693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105856693 - 1) / 3 = 35285564 from by norm_num]
      have h2 : (2 : ZMod 105856693) ^ 35285564 = ((37457946 : ℕ) : ZMod 105856693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105856693 - 1) / 31 = 3414732 from by norm_num]
      have h2 : (2 : ZMod 105856693) ^ 3414732 = ((74490792 : ℕ) : ZMod 105856693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105856693 - 1) / 284561 = 372 from by norm_num]
      have h2 : (2 : ZMod 105856693) ^ 372 = ((102209712 : ℕ) : ZMod 105856693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1465691771279 : Nat.Prime 1465691771279 := by
  refine lucas_primality 1465691771279 (7 : ZMod 1465691771279) ?_ (fun q hq hd => ?_)
  · rw [show 1465691771279 - 1 = 1465691771278 from by norm_num]
    reduce_mod_char
  · have e : 1465691771279 - 1 = [2 ^ 1, 7 ^ 1, 23 ^ 1, 43 ^ 1, 105856693 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1465691771279 - 1) / 2 = 732845885639 from by norm_num]
      have h2 : (7 : ZMod 1465691771279) ^ 732845885639 = ((1465691771278 : ℕ) : ZMod 1465691771279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1465691771279 - 1) / 7 = 209384538754 from by norm_num]
      have h2 : (7 : ZMod 1465691771279) ^ 209384538754 = ((37779811940 : ℕ) : ZMod 1465691771279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1465691771279 - 1) / 23 = 63725729186 from by norm_num]
      have h2 : (7 : ZMod 1465691771279) ^ 63725729186 = ((316402204564 : ℕ) : ZMod 1465691771279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1465691771279 - 1) / 43 = 34085855146 from by norm_num]
      have h2 : (7 : ZMod 1465691771279) ^ 34085855146 = ((835919138304 : ℕ) : ZMod 1465691771279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_105856693).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1465691771279 - 1) / 105856693 = 13846 from by norm_num]
      have h2 : (7 : ZMod 1465691771279) ^ 13846 = ((1371544109990 : ℕ) : ZMod 1465691771279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_32127963626435681 : Nat.Prime 32127963626435681 := by
  refine lucas_primality 32127963626435681 (3 : ZMod 32127963626435681) ?_ (fun q hq hd => ?_)
  · rw [show 32127963626435681 - 1 = 32127963626435680 from by norm_num]
    reduce_mod_char
  · have e : 32127963626435681 - 1 = [2 ^ 5, 5 ^ 1, 137 ^ 1, 1465691771279 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32127963626435681 - 1) / 2 = 16063981813217840 from by norm_num]
      have h2 : (3 : ZMod 32127963626435681) ^ 16063981813217840 = ((32127963626435680 : ℕ) : ZMod 32127963626435681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32127963626435681 - 1) / 5 = 6425592725287136 from by norm_num]
      have h2 : (3 : ZMod 32127963626435681) ^ 6425592725287136 = ((3333098599544525 : ℕ) : ZMod 32127963626435681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32127963626435681 - 1) / 137 = 234510683404640 from by norm_num]
      have h2 : (3 : ZMod 32127963626435681) ^ 234510683404640 = ((6353959802406229 : ℕ) : ZMod 32127963626435681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1465691771279).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32127963626435681 - 1) / 1465691771279 = 21920 from by norm_num]
      have h2 : (3 : ZMod 32127963626435681) ^ 21920 = ((11060083373860443 : ℕ) : ZMod 32127963626435681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_557272741 : Nat.Prime 557272741 := by
  refine lucas_primality 557272741 (6 : ZMod 557272741) ?_ (fun q hq hd => ?_)
  · rw [show 557272741 - 1 = 557272740 from by norm_num]
    reduce_mod_char
  · have e : 557272741 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 31 ^ 1, 53 ^ 1, 5653 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (557272741 - 1) / 2 = 278636370 from by norm_num]
      have h2 : (6 : ZMod 557272741) ^ 278636370 = ((557272740 : ℕ) : ZMod 557272741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (557272741 - 1) / 3 = 185757580 from by norm_num]
      have h2 : (6 : ZMod 557272741) ^ 185757580 = ((300932846 : ℕ) : ZMod 557272741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (557272741 - 1) / 5 = 111454548 from by norm_num]
      have h2 : (6 : ZMod 557272741) ^ 111454548 = ((514088453 : ℕ) : ZMod 557272741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (557272741 - 1) / 31 = 17976540 from by norm_num]
      have h2 : (6 : ZMod 557272741) ^ 17976540 = ((152515951 : ℕ) : ZMod 557272741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (557272741 - 1) / 53 = 10514580 from by norm_num]
      have h2 : (6 : ZMod 557272741) ^ 10514580 = ((344586399 : ℕ) : ZMod 557272741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (557272741 - 1) / 5653 = 98580 from by norm_num]
      have h2 : (6 : ZMod 557272741) ^ 98580 = ((483877389 : ℕ) : ZMod 557272741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_34033153146917030767 : Nat.Prime 34033153146917030767 := by
  refine lucas_primality 34033153146917030767 (3 : ZMod 34033153146917030767) ?_ (fun q hq hd => ?_)
  · rw [show 34033153146917030767 - 1 = 34033153146917030766 from by norm_num]
    reduce_mod_char
  · have e : 34033153146917030767 - 1 = [2 ^ 1, 3 ^ 4, 11 ^ 1, 34270993 ^ 1, 557272741 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34033153146917030767 - 1) / 2 = 17016576573458515383 from by norm_num]
      have h2 : (3 : ZMod 34033153146917030767) ^ 17016576573458515383 = ((34033153146917030766 : ℕ) : ZMod 34033153146917030767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34033153146917030767 - 1) / 3 = 11344384382305676922 from by norm_num]
      have h2 : (3 : ZMod 34033153146917030767) ^ 11344384382305676922 = ((2415022039490248754 : ℕ) : ZMod 34033153146917030767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34033153146917030767 - 1) / 11 = 3093923013356093706 from by norm_num]
      have h2 : (3 : ZMod 34033153146917030767) ^ 3093923013356093706 = ((4503664138327037824 : ℕ) : ZMod 34033153146917030767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34033153146917030767 - 1) / 34270993 = 993060024462 from by norm_num]
      have h2 : (3 : ZMod 34033153146917030767) ^ 993060024462 = ((7916242951858837885 : ℕ) : ZMod 34033153146917030767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_557272741).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34033153146917030767 - 1) / 557272741 = 61070909526 from by norm_num]
      have h2 : (3 : ZMod 34033153146917030767) ^ 61070909526 = ((2442573473260077311 : ℕ) : ZMod 34033153146917030767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_389054686774116311763206347 : Nat.Prime 389054686774116311763206347 := by
  refine lucas_primality 389054686774116311763206347 (2 : ZMod 389054686774116311763206347) ?_ (fun q hq hd => ?_)
  · rw [show 389054686774116311763206347 - 1 = 389054686774116311763206346 from by norm_num]
    reduce_mod_char
  · have e : 389054686774116311763206347 - 1 = [2 ^ 1, 3 ^ 3, 139 ^ 1, 1523 ^ 1, 34033153146917030767 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (389054686774116311763206347 - 1) / 2 = 194527343387058155881603173 from by norm_num]
      have h2 : (2 : ZMod 389054686774116311763206347) ^ 194527343387058155881603173 = ((389054686774116311763206346 : ℕ) : ZMod 389054686774116311763206347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (389054686774116311763206347 - 1) / 3 = 129684895591372103921068782 from by norm_num]
      have h2 : (2 : ZMod 389054686774116311763206347) ^ 129684895591372103921068782 = ((115448490482516310973945299 : ℕ) : ZMod 389054686774116311763206347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (389054686774116311763206347 - 1) / 139 = 2798954581108750444339614 from by norm_num]
      have h2 : (2 : ZMod 389054686774116311763206347) ^ 2798954581108750444339614 = ((208060140863638342382443458 : ℕ) : ZMod 389054686774116311763206347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (389054686774116311763206347 - 1) / 1523 = 255452847520759232937102 from by norm_num]
      have h2 : (2 : ZMod 389054686774116311763206347) ^ 255452847520759232937102 = ((197337025319799270068725285 : ℕ) : ZMod 389054686774116311763206347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_34033153146917030767).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (389054686774116311763206347 - 1) / 34033153146917030767 = 11431638 from by norm_num]
      have h2 : (2 : ZMod 389054686774116311763206347) ^ 11431638 = ((33707113382005143507261742 : ℕ) : ZMod 389054686774116311763206347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_51542639524661795300074174250365699 : Nat.Prime 51542639524661795300074174250365699 := by
  refine lucas_primality 51542639524661795300074174250365699 (3 : ZMod 51542639524661795300074174250365699) ?_ (fun q hq hd => ?_)
  · rw [show 51542639524661795300074174250365699 - 1 = 51542639524661795300074174250365698 from by norm_num]
    reduce_mod_char
  · have e : 51542639524661795300074174250365699 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 11 ^ 1, 139 ^ 1, 2063 ^ 1, 389054686774116311763206347 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51542639524661795300074174250365699 - 1) / 2 = 25771319762330897650037087125182849 from by norm_num]
      have h2 : (3 : ZMod 51542639524661795300074174250365699) ^ 25771319762330897650037087125182849 = ((51542639524661795300074174250365698 : ℕ) : ZMod 51542639524661795300074174250365699) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51542639524661795300074174250365699 - 1) / 3 = 17180879841553931766691391416788566 from by norm_num]
      have h2 : (3 : ZMod 51542639524661795300074174250365699) ^ 17180879841553931766691391416788566 = ((50476494123668339682375312419729203 : ℕ) : ZMod 51542639524661795300074174250365699) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51542639524661795300074174250365699 - 1) / 7 = 7363234217808827900010596321480814 from by norm_num]
      have h2 : (3 : ZMod 51542639524661795300074174250365699) ^ 7363234217808827900010596321480814 = ((1355414051740811765316185318072753 : ℕ) : ZMod 51542639524661795300074174250365699) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51542639524661795300074174250365699 - 1) / 11 = 4685694502241981390915834022760518 from by norm_num]
      have h2 : (3 : ZMod 51542639524661795300074174250365699) ^ 4685694502241981390915834022760518 = ((31637297087196904559524464100811247 : ℕ) : ZMod 51542639524661795300074174250365699) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51542639524661795300074174250365699 - 1) / 139 = 370810356292530901439382548563782 from by norm_num]
      have h2 : (3 : ZMod 51542639524661795300074174250365699) ^ 370810356292530901439382548563782 = ((16777216 : ℕ) : ZMod 51542639524661795300074174250365699) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51542639524661795300074174250365699 - 1) / 2063 = 24984313875260201308809585191646 from by norm_num]
      have h2 : (3 : ZMod 51542639524661795300074174250365699) ^ 24984313875260201308809585191646 = ((51237178829803828741074071628321050 : ℕ) : ZMod 51542639524661795300074174250365699) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_389054686774116311763206347).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51542639524661795300074174250365699 - 1) / 389054686774116311763206347 = 132481734 from by norm_num]
      have h2 : (3 : ZMod 51542639524661795300074174250365699) ^ 132481734 = ((9582198563674225369766819624681972 : ℕ) : ZMod 51542639524661795300074174250365699) := by
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

theorem prime_11281292593 : Nat.Prime 11281292593 := by
  refine lucas_primality 11281292593 (5 : ZMod 11281292593) ?_ (fun q hq hd => ?_)
  · rw [show 11281292593 - 1 = 11281292592 from by norm_num]
    reduce_mod_char
  · have e : 11281292593 - 1 = [2 ^ 4, 3 ^ 1, 163 ^ 1, 1441883 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11281292593 - 1) / 2 = 5640646296 from by norm_num]
      have h2 : (5 : ZMod 11281292593) ^ 5640646296 = ((11281292592 : ℕ) : ZMod 11281292593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11281292593 - 1) / 3 = 3760430864 from by norm_num]
      have h2 : (5 : ZMod 11281292593) ^ 3760430864 = ((5012914318 : ℕ) : ZMod 11281292593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11281292593 - 1) / 163 = 69210384 from by norm_num]
      have h2 : (5 : ZMod 11281292593) ^ 69210384 = ((10744421681 : ℕ) : ZMod 11281292593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11281292593 - 1) / 1441883 = 7824 from by norm_num]
      have h2 : (5 : ZMod 11281292593) ^ 7824 = ((6708663093 : ℕ) : ZMod 11281292593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8562191377 : Nat.Prime 8562191377 := by
  refine lucas_primality 8562191377 (5 : ZMod 8562191377) ?_ (fun q hq hd => ?_)
  · rw [show 8562191377 - 1 = 8562191376 from by norm_num]
    reduce_mod_char
  · have e : 8562191377 - 1 = [2 ^ 4, 3 ^ 1, 41 ^ 1, 4350707 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8562191377 - 1) / 2 = 4281095688 from by norm_num]
      have h2 : (5 : ZMod 8562191377) ^ 4281095688 = ((8562191376 : ℕ) : ZMod 8562191377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8562191377 - 1) / 3 = 2854063792 from by norm_num]
      have h2 : (5 : ZMod 8562191377) ^ 2854063792 = ((4919935323 : ℕ) : ZMod 8562191377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8562191377 - 1) / 41 = 208833936 from by norm_num]
      have h2 : (5 : ZMod 8562191377) ^ 208833936 = ((6050239875 : ℕ) : ZMod 8562191377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8562191377 - 1) / 4350707 = 1968 from by norm_num]
      have h2 : (5 : ZMod 8562191377) ^ 1968 = ((8424328877 : ℕ) : ZMod 8562191377) := by
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

theorem prime_35374479827 : Nat.Prime 35374479827 := by
  refine lucas_primality 35374479827 (7 : ZMod 35374479827) ?_ (fun q hq hd => ?_)
  · rw [show 35374479827 - 1 = 35374479826 from by norm_num]
    reduce_mod_char
  · have e : 35374479827 - 1 = [2 ^ 1, 7 ^ 1, 23 ^ 1, 173 ^ 1, 635021 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35374479827 - 1) / 2 = 17687239913 from by norm_num]
      have h2 : (7 : ZMod 35374479827) ^ 17687239913 = ((35374479826 : ℕ) : ZMod 35374479827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35374479827 - 1) / 7 = 5053497118 from by norm_num]
      have h2 : (7 : ZMod 35374479827) ^ 5053497118 = ((16285941327 : ℕ) : ZMod 35374479827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35374479827 - 1) / 23 = 1538020862 from by norm_num]
      have h2 : (7 : ZMod 35374479827) ^ 1538020862 = ((12909266343 : ℕ) : ZMod 35374479827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35374479827 - 1) / 173 = 204476762 from by norm_num]
      have h2 : (7 : ZMod 35374479827) ^ 204476762 = ((1474550170 : ℕ) : ZMod 35374479827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35374479827 - 1) / 635021 = 55706 from by norm_num]
      have h2 : (7 : ZMod 35374479827) ^ 55706 = ((16123704047 : ℕ) : ZMod 35374479827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2947873319 : Nat.Prime 2947873319 := by
  refine lucas_primality 2947873319 (19 : ZMod 2947873319) ?_ (fun q hq hd => ?_)
  · rw [show 2947873319 - 1 = 2947873318 from by norm_num]
    reduce_mod_char
  · have e : 2947873319 - 1 = [2 ^ 1, 13 ^ 1, 83 ^ 1, 1366021 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2947873319 - 1) / 2 = 1473936659 from by norm_num]
      have h2 : (19 : ZMod 2947873319) ^ 1473936659 = ((2947873318 : ℕ) : ZMod 2947873319) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2947873319 - 1) / 13 = 226759486 from by norm_num]
      have h2 : (19 : ZMod 2947873319) ^ 226759486 = ((275805639 : ℕ) : ZMod 2947873319) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2947873319 - 1) / 83 = 35516546 from by norm_num]
      have h2 : (19 : ZMod 2947873319) ^ 35516546 = ((438036658 : ℕ) : ZMod 2947873319) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2947873319 - 1) / 1366021 = 2158 from by norm_num]
      have h2 : (19 : ZMod 2947873319) ^ 2158 = ((1645050476 : ℕ) : ZMod 2947873319) := by
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

theorem prime_378440669 : Nat.Prime 378440669 := by
  refine lucas_primality 378440669 (2 : ZMod 378440669) ?_ (fun q hq hd => ?_)
  · rw [show 378440669 - 1 = 378440668 from by norm_num]
    reduce_mod_char
  · have e : 378440669 - 1 = [2 ^ 2, 2609 ^ 1, 36263 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (378440669 - 1) / 2 = 189220334 from by norm_num]
      have h2 : (2 : ZMod 378440669) ^ 189220334 = ((378440668 : ℕ) : ZMod 378440669) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (378440669 - 1) / 2609 = 145052 from by norm_num]
      have h2 : (2 : ZMod 378440669) ^ 145052 = ((168468035 : ℕ) : ZMod 378440669) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (378440669 - 1) / 36263 = 10436 from by norm_num]
      have h2 : (2 : ZMod 378440669) ^ 10436 = ((155303256 : ℕ) : ZMod 378440669) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2941122807484708981283 : Nat.Prime 2941122807484708981283 := by
  refine lucas_primality 2941122807484708981283 (2 : ZMod 2941122807484708981283) ?_ (fun q hq hd => ?_)
  · rw [show 2941122807484708981283 - 1 = 2941122807484708981282 from by norm_num]
    reduce_mod_char
  · have e : 2941122807484708981283 - 1 = [2 ^ 1, 372653 ^ 1, 10427513 ^ 1, 378440669 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2941122807484708981283 - 1) / 2 = 1470561403742354490641 from by norm_num]
      have h2 : (2 : ZMod 2941122807484708981283) ^ 1470561403742354490641 = ((2941122807484708981282 : ℕ) : ZMod 2941122807484708981283) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2941122807484708981283 - 1) / 372653 = 7892389991452394 from by norm_num]
      have h2 : (2 : ZMod 2941122807484708981283) ^ 7892389991452394 = ((1887588702401834344217 : ℕ) : ZMod 2941122807484708981283) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2941122807484708981283 - 1) / 10427513 = 282054101249714 from by norm_num]
      have h2 : (2 : ZMod 2941122807484708981283) ^ 282054101249714 = ((2345825179295757799339 : ℕ) : ZMod 2941122807484708981283) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_378440669).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2941122807484708981283 - 1) / 378440669 = 7771688003978 from by norm_num]
      have h2 : (2 : ZMod 2941122807484708981283) ^ 7771688003978 = ((2513942153412753592631 : ℕ) : ZMod 2941122807484708981283) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_31946475934898908954695947 : Nat.Prime 31946475934898908954695947 := by
  refine lucas_primality 31946475934898908954695947 (2 : ZMod 31946475934898908954695947) ?_ (fun q hq hd => ?_)
  · rw [show 31946475934898908954695947 - 1 = 31946475934898908954695946 from by norm_num]
    reduce_mod_char
  · have e : 31946475934898908954695947 - 1 = [2 ^ 1, 5431 ^ 1, 2941122807484708981283 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31946475934898908954695947 - 1) / 2 = 15973237967449454477347973 from by norm_num]
      have h2 : (2 : ZMod 31946475934898908954695947) ^ 15973237967449454477347973 = ((31946475934898908954695946 : ℕ) : ZMod 31946475934898908954695947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31946475934898908954695947 - 1) / 5431 = 5882245614969417962566 from by norm_num]
      have h2 : (2 : ZMod 31946475934898908954695947) ^ 5882245614969417962566 = ((689366381517021619362917 : ℕ) : ZMod 31946475934898908954695947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2941122807484708981283).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31946475934898908954695947 - 1) / 2941122807484708981283 = 10862 from by norm_num]
      have h2 : (2 : ZMod 31946475934898908954695947) ^ 10862 = ((28280308790206871928974930 : ℕ) : ZMod 31946475934898908954695947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_138456026701851871409652234299 : Nat.Prime 138456026701851871409652234299 := by
  refine lucas_primality 138456026701851871409652234299 (2 : ZMod 138456026701851871409652234299) ?_ (fun q hq hd => ?_)
  · rw [show 138456026701851871409652234299 - 1 = 138456026701851871409652234298 from by norm_num]
    reduce_mod_char
  · have e : 138456026701851871409652234299 - 1 = [2 ^ 1, 11 ^ 1, 197 ^ 1, 31946475934898908954695947 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138456026701851871409652234299 - 1) / 2 = 69228013350925935704826117149 from by norm_num]
      have h2 : (2 : ZMod 138456026701851871409652234299) ^ 69228013350925935704826117149 = ((138456026701851871409652234298 : ℕ) : ZMod 138456026701851871409652234299) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138456026701851871409652234299 - 1) / 11 = 12586911518350170128150203118 from by norm_num]
      have h2 : (2 : ZMod 138456026701851871409652234299) ^ 12586911518350170128150203118 = ((65675874587384098548674240074 : ℕ) : ZMod 138456026701851871409652234299) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138456026701851871409652234299 - 1) / 197 = 702822470567775997003310834 from by norm_num]
      have h2 : (2 : ZMod 138456026701851871409652234299) ^ 702822470567775997003310834 = ((31987782116399116976719034142 : ℕ) : ZMod 138456026701851871409652234299) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_31946475934898908954695947).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138456026701851871409652234299 - 1) / 31946475934898908954695947 = 4334 from by norm_num]
      have h2 : (2 : ZMod 138456026701851871409652234299) ^ 4334 = ((130514409753058423738650491675 : ℕ) : ZMod 138456026701851871409652234299) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_68928073 : Nat.Prime 68928073 := by
  refine lucas_primality 68928073 (5 : ZMod 68928073) ?_ (fun q hq hd => ?_)
  · rw [show 68928073 - 1 = 68928072 from by norm_num]
    reduce_mod_char
  · have e : 68928073 - 1 = [2 ^ 3, 3 ^ 1, 2872003 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68928073 - 1) / 2 = 34464036 from by norm_num]
      have h2 : (5 : ZMod 68928073) ^ 34464036 = ((68928072 : ℕ) : ZMod 68928073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68928073 - 1) / 3 = 22976024 from by norm_num]
      have h2 : (5 : ZMod 68928073) ^ 22976024 = ((31030581 : ℕ) : ZMod 68928073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68928073 - 1) / 2872003 = 24 from by norm_num]
      have h2 : (5 : ZMod 68928073) ^ 24 = ((52800575 : ℕ) : ZMod 68928073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2191165825376888084750157716424579062015865776131 : Nat.Prime 2191165825376888084750157716424579062015865776131 := by
  refine lucas_primality 2191165825376888084750157716424579062015865776131 (10 : ZMod 2191165825376888084750157716424579062015865776131) ?_ (fun q hq hd => ?_)
  · rw [show 2191165825376888084750157716424579062015865776131 - 1 = 2191165825376888084750157716424579062015865776130 from by norm_num]
    reduce_mod_char
  · have e : 2191165825376888084750157716424579062015865776131 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 11 ^ 2, 17 ^ 1, 31 ^ 1, 257 ^ 1, 467 ^ 1, 68928073 ^ 1, 138456026701851871409652234299 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191165825376888084750157716424579062015865776131 - 1) / 2 = 1095582912688444042375078858212289531007932888065 from by norm_num]
      have h2 : (10 : ZMod 2191165825376888084750157716424579062015865776131) ^ 1095582912688444042375078858212289531007932888065 = ((2191165825376888084750157716424579062015865776130 : ℕ) : ZMod 2191165825376888084750157716424579062015865776131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191165825376888084750157716424579062015865776131 - 1) / 3 = 730388608458962694916719238808193020671955258710 from by norm_num]
      have h2 : (10 : ZMod 2191165825376888084750157716424579062015865776131) ^ 730388608458962694916719238808193020671955258710 = ((1582923984765994920332564776161139931125203015861 : ℕ) : ZMod 2191165825376888084750157716424579062015865776131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191165825376888084750157716424579062015865776131 - 1) / 5 = 438233165075377616950031543284915812403173155226 from by norm_num]
      have h2 : (10 : ZMod 2191165825376888084750157716424579062015865776131) ^ 438233165075377616950031543284915812403173155226 = ((979053620280778553669658157702917569699132060798 : ℕ) : ZMod 2191165825376888084750157716424579062015865776131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191165825376888084750157716424579062015865776131 - 1) / 11 = 199196893216080734977287065129507187455987797830 from by norm_num]
      have h2 : (10 : ZMod 2191165825376888084750157716424579062015865776131) ^ 199196893216080734977287065129507187455987797830 = ((2191165825376223470752265258488127158485725603843 : ℕ) : ZMod 2191165825376888084750157716424579062015865776131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191165825376888084750157716424579062015865776131 - 1) / 17 = 128892107375111063808832806848504650706815633890 from by norm_num]
      have h2 : (10 : ZMod 2191165825376888084750157716424579062015865776131) ^ 128892107375111063808832806848504650706815633890 = ((17592186044416 : ℕ) : ZMod 2191165825376888084750157716424579062015865776131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191165825376888084750157716424579062015865776131 - 1) / 31 = 70682768560544776927424442465309002000511799230 from by norm_num]
      have h2 : (10 : ZMod 2191165825376888084750157716424579062015865776131) ^ 70682768560544776927424442465309002000511799230 = ((992892867990455659262784019633749190896332904998 : ℕ) : ZMod 2191165825376888084750157716424579062015865776131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191165825376888084750157716424579062015865776131 - 1) / 257 = 8525937063723299940662092281807700630411929090 from by norm_num]
      have h2 : (10 : ZMod 2191165825376888084750157716424579062015865776131) ^ 8525937063723299940662092281807700630411929090 = ((76450698885047487477065925951557350805265345527 : ℕ) : ZMod 2191165825376888084750157716424579062015865776131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191165825376888084750157716424579062015865776131 - 1) / 467 = 4692003908729953072270145003050490496821982390 from by norm_num]
      have h2 : (10 : ZMod 2191165825376888084750157716424579062015865776131) ^ 4692003908729953072270145003050490496821982390 = ((610417348794799989495399486171271762540526642834 : ℕ) : ZMod 2191165825376888084750157716424579062015865776131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_68928073).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191165825376888084750157716424579062015865776131 - 1) / 68928073 = 31789164124418335106367440685953589069810 from by norm_num]
      have h2 : (10 : ZMod 2191165825376888084750157716424579062015865776131) ^ 31789164124418335106367440685953589069810 = ((304653436188293073278172659118857538423379691881 : ℕ) : ZMod 2191165825376888084750157716424579062015865776131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_138456026701851871409652234299).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191165825376888084750157716424579062015865776131 - 1) / 138456026701851871409652234299 = 15825716493333264870 from by norm_num]
      have h2 : (10 : ZMod 2191165825376888084750157716424579062015865776131) ^ 15825716493333264870 = ((777705360057785425290312946276293716477408712273 : ℕ) : ZMod 2191165825376888084750157716424579062015865776131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_683926141 : Nat.Prime 683926141 := by
  refine lucas_primality 683926141 (2 : ZMod 683926141) ?_ (fun q hq hd => ?_)
  · rw [show 683926141 - 1 = 683926140 from by norm_num]
    reduce_mod_char
  · have e : 683926141 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 29 ^ 1, 47 ^ 1, 8363 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (683926141 - 1) / 2 = 341963070 from by norm_num]
      have h2 : (2 : ZMod 683926141) ^ 341963070 = ((683926140 : ℕ) : ZMod 683926141) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (683926141 - 1) / 3 = 227975380 from by norm_num]
      have h2 : (2 : ZMod 683926141) ^ 227975380 = ((520643691 : ℕ) : ZMod 683926141) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (683926141 - 1) / 5 = 136785228 from by norm_num]
      have h2 : (2 : ZMod 683926141) ^ 136785228 = ((47696074 : ℕ) : ZMod 683926141) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (683926141 - 1) / 29 = 23583660 from by norm_num]
      have h2 : (2 : ZMod 683926141) ^ 23583660 = ((256335422 : ℕ) : ZMod 683926141) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (683926141 - 1) / 47 = 14551620 from by norm_num]
      have h2 : (2 : ZMod 683926141) ^ 14551620 = ((448575279 : ℕ) : ZMod 683926141) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (683926141 - 1) / 8363 = 81780 from by norm_num]
      have h2 : (2 : ZMod 683926141) ^ 81780 = ((289079530 : ℕ) : ZMod 683926141) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_14231135141929 : Nat.Prime 14231135141929 := by
  refine lucas_primality 14231135141929 (7 : ZMod 14231135141929) ?_ (fun q hq hd => ?_)
  · rw [show 14231135141929 - 1 = 14231135141928 from by norm_num]
    reduce_mod_char
  · have e : 14231135141929 - 1 = [2 ^ 3, 3 ^ 2, 17 ^ 2, 683926141 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14231135141929 - 1) / 2 = 7115567570964 from by norm_num]
      have h2 : (7 : ZMod 14231135141929) ^ 7115567570964 = ((14231135141928 : ℕ) : ZMod 14231135141929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14231135141929 - 1) / 3 = 4743711713976 from by norm_num]
      have h2 : (7 : ZMod 14231135141929) ^ 4743711713976 = ((3341890225393 : ℕ) : ZMod 14231135141929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14231135141929 - 1) / 17 = 837125596584 from by norm_num]
      have h2 : (7 : ZMod 14231135141929) ^ 837125596584 = ((10508603080810 : ℕ) : ZMod 14231135141929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_683926141).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14231135141929 - 1) / 683926141 = 20808 from by norm_num]
      have h2 : (7 : ZMod 14231135141929) ^ 20808 = ((5970798221395 : ℕ) : ZMod 14231135141929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1198107457 : Nat.Prime 1198107457 := by
  refine lucas_primality 1198107457 (5 : ZMod 1198107457) ?_ (fun q hq hd => ?_)
  · rw [show 1198107457 - 1 = 1198107456 from by norm_num]
    reduce_mod_char
  · have e : 1198107457 - 1 = [2 ^ 6, 3 ^ 1, 7 ^ 1, 13 ^ 1, 47 ^ 1, 1459 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1198107457 - 1) / 2 = 599053728 from by norm_num]
      have h2 : (5 : ZMod 1198107457) ^ 599053728 = ((1198107456 : ℕ) : ZMod 1198107457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1198107457 - 1) / 3 = 399369152 from by norm_num]
      have h2 : (5 : ZMod 1198107457) ^ 399369152 = ((1164777170 : ℕ) : ZMod 1198107457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1198107457 - 1) / 7 = 171158208 from by norm_num]
      have h2 : (5 : ZMod 1198107457) ^ 171158208 = ((884536516 : ℕ) : ZMod 1198107457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1198107457 - 1) / 13 = 92162112 from by norm_num]
      have h2 : (5 : ZMod 1198107457) ^ 92162112 = ((641842961 : ℕ) : ZMod 1198107457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1198107457 - 1) / 47 = 25491648 from by norm_num]
      have h2 : (5 : ZMod 1198107457) ^ 25491648 = ((646705831 : ℕ) : ZMod 1198107457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1198107457 - 1) / 1459 = 821184 from by norm_num]
      have h2 : (5 : ZMod 1198107457) ^ 821184 = ((1030286803 : ℕ) : ZMod 1198107457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_599053729 : Nat.Prime 599053729 := by
  refine lucas_primality 599053729 (11 : ZMod 599053729) ?_ (fun q hq hd => ?_)
  · rw [show 599053729 - 1 = 599053728 from by norm_num]
    reduce_mod_char
  · have e : 599053729 - 1 = [2 ^ 5, 3 ^ 1, 7 ^ 1, 13 ^ 1, 47 ^ 1, 1459 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (599053729 - 1) / 2 = 299526864 from by norm_num]
      have h2 : (11 : ZMod 599053729) ^ 299526864 = ((599053728 : ℕ) : ZMod 599053729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (599053729 - 1) / 3 = 199684576 from by norm_num]
      have h2 : (11 : ZMod 599053729) ^ 199684576 = ((239477023 : ℕ) : ZMod 599053729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (599053729 - 1) / 7 = 85579104 from by norm_num]
      have h2 : (11 : ZMod 599053729) ^ 85579104 = ((584915206 : ℕ) : ZMod 599053729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (599053729 - 1) / 13 = 46081056 from by norm_num]
      have h2 : (11 : ZMod 599053729) ^ 46081056 = ((404262688 : ℕ) : ZMod 599053729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (599053729 - 1) / 47 = 12745824 from by norm_num]
      have h2 : (11 : ZMod 599053729) ^ 12745824 = ((89298343 : ℕ) : ZMod 599053729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (599053729 - 1) / 1459 = 410592 from by norm_num]
      have h2 : (11 : ZMod 599053729) ^ 410592 = ((560073907 : ℕ) : ZMod 599053729) := by
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

theorem prime_1871670769 : Nat.Prime 1871670769 := by
  refine lucas_primality 1871670769 (13 : ZMod 1871670769) ?_ (fun q hq hd => ?_)
  · rw [show 1871670769 - 1 = 1871670768 from by norm_num]
    reduce_mod_char
  · have e : 1871670769 - 1 = [2 ^ 4, 3 ^ 1, 11 ^ 1, 193 ^ 1, 18367 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1871670769 - 1) / 2 = 935835384 from by norm_num]
      have h2 : (13 : ZMod 1871670769) ^ 935835384 = ((1871670768 : ℕ) : ZMod 1871670769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1871670769 - 1) / 3 = 623890256 from by norm_num]
      have h2 : (13 : ZMod 1871670769) ^ 623890256 = ((1587618531 : ℕ) : ZMod 1871670769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1871670769 - 1) / 11 = 170151888 from by norm_num]
      have h2 : (13 : ZMod 1871670769) ^ 170151888 = ((1668222630 : ℕ) : ZMod 1871670769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1871670769 - 1) / 193 = 9697776 from by norm_num]
      have h2 : (13 : ZMod 1871670769) ^ 9697776 = ((22899189 : ℕ) : ZMod 1871670769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1871670769 - 1) / 18367 = 101904 from by norm_num]
      have h2 : (13 : ZMod 1871670769) ^ 101904 = ((977675838 : ℕ) : ZMod 1871670769) := by
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

theorem prime_82471201 : Nat.Prime 82471201 := by
  refine lucas_primality 82471201 (11 : ZMod 82471201) ?_ (fun q hq hd => ?_)
  · rw [show 82471201 - 1 = 82471200 from by norm_num]
    reduce_mod_char
  · have e : 82471201 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 2, 7 ^ 1, 4909 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82471201 - 1) / 2 = 41235600 from by norm_num]
      have h2 : (11 : ZMod 82471201) ^ 41235600 = ((82471200 : ℕ) : ZMod 82471201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82471201 - 1) / 3 = 27490400 from by norm_num]
      have h2 : (11 : ZMod 82471201) ^ 27490400 = ((66304449 : ℕ) : ZMod 82471201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82471201 - 1) / 5 = 16494240 from by norm_num]
      have h2 : (11 : ZMod 82471201) ^ 16494240 = ((76895157 : ℕ) : ZMod 82471201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82471201 - 1) / 7 = 11781600 from by norm_num]
      have h2 : (11 : ZMod 82471201) ^ 11781600 = ((37103845 : ℕ) : ZMod 82471201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82471201 - 1) / 4909 = 16800 from by norm_num]
      have h2 : (11 : ZMod 82471201) ^ 16800 = ((49182883 : ℕ) : ZMod 82471201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1562147729 : Nat.Prime 1562147729 := by
  refine lucas_primality 1562147729 (3 : ZMod 1562147729) ?_ (fun q hq hd => ?_)
  · rw [show 1562147729 - 1 = 1562147728 from by norm_num]
    reduce_mod_char
  · have e : 1562147729 - 1 = [2 ^ 4, 4603 ^ 1, 21211 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1562147729 - 1) / 2 = 781073864 from by norm_num]
      have h2 : (3 : ZMod 1562147729) ^ 781073864 = ((1562147728 : ℕ) : ZMod 1562147729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1562147729 - 1) / 4603 = 339376 from by norm_num]
      have h2 : (3 : ZMod 1562147729) ^ 339376 = ((33694782 : ℕ) : ZMod 1562147729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1562147729 - 1) / 21211 = 73648 from by norm_num]
      have h2 : (3 : ZMod 1562147729) ^ 73648 = ((338384575 : ℕ) : ZMod 1562147729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2543176502813 : Nat.Prime 2543176502813 := by
  refine lucas_primality 2543176502813 (2 : ZMod 2543176502813) ?_ (fun q hq hd => ?_)
  · rw [show 2543176502813 - 1 = 2543176502812 from by norm_num]
    reduce_mod_char
  · have e : 2543176502813 - 1 = [2 ^ 2, 11 ^ 1, 37 ^ 1, 1562147729 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2543176502813 - 1) / 2 = 1271588251406 from by norm_num]
      have h2 : (2 : ZMod 2543176502813) ^ 1271588251406 = ((2543176502812 : ℕ) : ZMod 2543176502813) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2543176502813 - 1) / 11 = 231197863892 from by norm_num]
      have h2 : (2 : ZMod 2543176502813) ^ 231197863892 = ((1448839021752 : ℕ) : ZMod 2543176502813) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2543176502813 - 1) / 37 = 68734500076 from by norm_num]
      have h2 : (2 : ZMod 2543176502813) ^ 68734500076 = ((1680753671471 : ℕ) : ZMod 2543176502813) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1562147729).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2543176502813 - 1) / 1562147729 = 1628 from by norm_num]
      have h2 : (2 : ZMod 2543176502813) ^ 1628 = ((1152398248949 : ℕ) : ZMod 2543176502813) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_661225890731381 : Nat.Prime 661225890731381 := by
  refine lucas_primality 661225890731381 (2 : ZMod 661225890731381) ?_ (fun q hq hd => ?_)
  · rw [show 661225890731381 - 1 = 661225890731380 from by norm_num]
    reduce_mod_char
  · have e : 661225890731381 - 1 = [2 ^ 2, 5 ^ 1, 13 ^ 1, 2543176502813 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (661225890731381 - 1) / 2 = 330612945365690 from by norm_num]
      have h2 : (2 : ZMod 661225890731381) ^ 330612945365690 = ((661225890731380 : ℕ) : ZMod 661225890731381) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (661225890731381 - 1) / 5 = 132245178146276 from by norm_num]
      have h2 : (2 : ZMod 661225890731381) ^ 132245178146276 = ((17175367711099 : ℕ) : ZMod 661225890731381) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (661225890731381 - 1) / 13 = 50863530056260 from by norm_num]
      have h2 : (2 : ZMod 661225890731381) ^ 50863530056260 = ((598628601456984 : ℕ) : ZMod 661225890731381) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2543176502813).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (661225890731381 - 1) / 2543176502813 = 260 from by norm_num]
      have h2 : (2 : ZMod 661225890731381) ^ 260 = ((373168197789953 : ℕ) : ZMod 661225890731381) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_99183883609707151 : Nat.Prime 99183883609707151 := by
  refine lucas_primality 99183883609707151 (15 : ZMod 99183883609707151) ?_ (fun q hq hd => ?_)
  · rw [show 99183883609707151 - 1 = 99183883609707150 from by norm_num]
    reduce_mod_char
  · have e : 99183883609707151 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 2, 661225890731381 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99183883609707151 - 1) / 2 = 49591941804853575 from by norm_num]
      have h2 : (15 : ZMod 99183883609707151) ^ 49591941804853575 = ((99183883609707150 : ℕ) : ZMod 99183883609707151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99183883609707151 - 1) / 3 = 33061294536569050 from by norm_num]
      have h2 : (15 : ZMod 99183883609707151) ^ 33061294536569050 = ((60059586611823297 : ℕ) : ZMod 99183883609707151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99183883609707151 - 1) / 5 = 19836776721941430 from by norm_num]
      have h2 : (15 : ZMod 99183883609707151) ^ 19836776721941430 = ((13127976209638683 : ℕ) : ZMod 99183883609707151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_661225890731381).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99183883609707151 - 1) / 661225890731381 = 150 from by norm_num]
      have h2 : (15 : ZMod 99183883609707151) ^ 150 = ((2188827200044268 : ℕ) : ZMod 99183883609707151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6963303732703100243107 : Nat.Prime 6963303732703100243107 := by
  refine lucas_primality 6963303732703100243107 (5 : ZMod 6963303732703100243107) ?_ (fun q hq hd => ?_)
  · rw [show 6963303732703100243107 - 1 = 6963303732703100243106 from by norm_num]
    reduce_mod_char
  · have e : 6963303732703100243107 - 1 = [2 ^ 1, 3 ^ 1, 11701 ^ 1, 99183883609707151 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6963303732703100243107 - 1) / 2 = 3481651866351550121553 from by norm_num]
      have h2 : (5 : ZMod 6963303732703100243107) ^ 3481651866351550121553 = ((6963303732703100243106 : ℕ) : ZMod 6963303732703100243107) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6963303732703100243107 - 1) / 3 = 2321101244234366747702 from by norm_num]
      have h2 : (5 : ZMod 6963303732703100243107) ^ 2321101244234366747702 = ((2566477849796228817663 : ℕ) : ZMod 6963303732703100243107) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6963303732703100243107 - 1) / 11701 = 595103301658242906 from by norm_num]
      have h2 : (5 : ZMod 6963303732703100243107) ^ 595103301658242906 = ((1792681776384858841398 : ℕ) : ZMod 6963303732703100243107) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_99183883609707151).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6963303732703100243107 - 1) / 99183883609707151 = 70206 from by norm_num]
      have h2 : (5 : ZMod 6963303732703100243107) ^ 70206 = ((448529110241174888592 : ℕ) : ZMod 6963303732703100243107) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_414570151 : Nat.Prime 414570151 := by
  refine lucas_primality 414570151 (3 : ZMod 414570151) ?_ (fun q hq hd => ?_)
  · rw [show 414570151 - 1 = 414570150 from by norm_num]
    reduce_mod_char
  · have e : 414570151 - 1 = [2 ^ 1, 3 ^ 5, 5 ^ 2, 149 ^ 1, 229 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (414570151 - 1) / 2 = 207285075 from by norm_num]
      have h2 : (3 : ZMod 414570151) ^ 207285075 = ((414570150 : ℕ) : ZMod 414570151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (414570151 - 1) / 3 = 138190050 from by norm_num]
      have h2 : (3 : ZMod 414570151) ^ 138190050 = ((412609671 : ℕ) : ZMod 414570151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (414570151 - 1) / 5 = 82914030 from by norm_num]
      have h2 : (3 : ZMod 414570151) ^ 82914030 = ((146670516 : ℕ) : ZMod 414570151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (414570151 - 1) / 149 = 2782350 from by norm_num]
      have h2 : (3 : ZMod 414570151) ^ 2782350 = ((111358274 : ℕ) : ZMod 414570151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (414570151 - 1) / 229 = 1810350 from by norm_num]
      have h2 : (3 : ZMod 414570151) ^ 1810350 = ((54141314 : ℕ) : ZMod 414570151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1150846739177 : Nat.Prime 1150846739177 := by
  refine lucas_primality 1150846739177 (3 : ZMod 1150846739177) ?_ (fun q hq hd => ?_)
  · rw [show 1150846739177 - 1 = 1150846739176 from by norm_num]
    reduce_mod_char
  · have e : 1150846739177 - 1 = [2 ^ 3, 347 ^ 1, 414570151 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1150846739177 - 1) / 2 = 575423369588 from by norm_num]
      have h2 : (3 : ZMod 1150846739177) ^ 575423369588 = ((1150846739176 : ℕ) : ZMod 1150846739177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1150846739177 - 1) / 347 = 3316561208 from by norm_num]
      have h2 : (3 : ZMod 1150846739177) ^ 3316561208 = ((8169306114 : ℕ) : ZMod 1150846739177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_414570151).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1150846739177 - 1) / 414570151 = 2776 from by norm_num]
      have h2 : (3 : ZMod 1150846739177) ^ 2776 = ((387971033855 : ℕ) : ZMod 1150846739177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_275509565477848842604777623828011666349761 : Nat.Prime 275509565477848842604777623828011666349761 := by
  refine lucas_primality 275509565477848842604777623828011666349761 (3 : ZMod 275509565477848842604777623828011666349761) ?_ (fun q hq hd => ?_)
  · rw [show 275509565477848842604777623828011666349761 - 1 = 275509565477848842604777623828011666349760 from by norm_num]
    reduce_mod_char
  · have e : 275509565477848842604777623828011666349761 - 1 = [2 ^ 6, 5 ^ 1, 11 ^ 1, 9767 ^ 1, 1150846739177 ^ 1, 6963303732703100243107 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (275509565477848842604777623828011666349761 - 1) / 2 = 137754782738924421302388811914005833174880 from by norm_num]
      have h2 : (3 : ZMod 275509565477848842604777623828011666349761) ^ 137754782738924421302388811914005833174880 = ((275509565477848842604777623828011666349760 : ℕ) : ZMod 275509565477848842604777623828011666349761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (275509565477848842604777623828011666349761 - 1) / 5 = 55101913095569768520955524765602333269952 from by norm_num]
      have h2 : (3 : ZMod 275509565477848842604777623828011666349761) ^ 55101913095569768520955524765602333269952 = ((172605400291551663578437633522845003856932 : ℕ) : ZMod 275509565477848842604777623828011666349761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (275509565477848842604777623828011666349761 - 1) / 11 = 25046324134349894782252511257091969668160 from by norm_num]
      have h2 : (3 : ZMod 275509565477848842604777623828011666349761) ^ 25046324134349894782252511257091969668160 = ((15529605175133109451269257420583468350225 : ℕ) : ZMod 275509565477848842604777623828011666349761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (275509565477848842604777623828011666349761 - 1) / 9767 = 28208207789274991563917029162282345280 from by norm_num]
      have h2 : (3 : ZMod 275509565477848842604777623828011666349761) ^ 28208207789274991563917029162282345280 = ((95322848893309812362064735768478561784825 : ℕ) : ZMod 275509565477848842604777623828011666349761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1150846739177).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (275509565477848842604777623828011666349761 - 1) / 1150846739177 = 239397268201735353861979762880 from by norm_num]
      have h2 : (3 : ZMod 275509565477848842604777623828011666349761) ^ 239397268201735353861979762880 = ((165492474927749271232929161870655134133249 : ℕ) : ZMod 275509565477848842604777623828011666349761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6963303732703100243107).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (275509565477848842604777623828011666349761 - 1) / 6963303732703100243107 = 39565926757426991680 from by norm_num]
      have h2 : (3 : ZMod 275509565477848842604777623828011666349761) ^ 39565926757426991680 = ((4706538208105029075721189263873113425481 : ℕ) : ZMod 275509565477848842604777623828011666349761) := by
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

theorem prime_8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 : Nat.Prime 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 := by
  refine lucas_primality 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ?_ (fun q hq hd => ?_)
  · rw [show 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1 = 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499760 from by norm_num]
    reduce_mod_char
  · have e : 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 23 ^ 1, 89 ^ 1, 257 ^ 1, 353 ^ 1, 397 ^ 1, 683 ^ 1, 2113 ^ 1, 65537 ^ 1, 229153 ^ 1, 5304641 ^ 1, 119782433 ^ 1, 2931542417 ^ 1, 43872038849 ^ 1, 275509565477848842604777623828011666349761 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 2 = 4317173865393075786561545214686281300322945861963823291741343697669501884401853756367093747030824821749880 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 4317173865393075786561545214686281300322945861963823291741343697669501884401853756367093747030824821749880 = ((8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499760 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 3 = 2878115910262050524374363476457520866881963907975882194494229131779667922934569170911395831353883214499920 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 2878115910262050524374363476457520866881963907975882194494229131779667922934569170911395831353883214499920 = ((776454806447972375652201310454734096806608525911713117153739080410073517715431076734859089664201038953159 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 5 = 1726869546157230314624618085874512520129178344785529316696537479067800753760741502546837498812329928699952 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 1726869546157230314624618085874512520129178344785529316696537479067800753760741502546837498812329928699952 = ((4839865516175155805574003659638339445236474080431519561317140997513626928998438998492661827233536283010463 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 23 = 375406423077658764048830018668372286984603987996854199281855973710391468208856848379747282350506506239120 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 375406423077658764048830018668372286984603987996854199281855973710391468208856848379747282350506506239120 = ((624951187537688898149307179500956631676396599830010215239150030139787520617925236998812911686513392020314 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 89 = 97015143042541028911495398082837782029729120493569062735760532531898918750603455199260533641142130825840 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 97015143042541028911495398082837782029729120493569062735760532531898918750603455199260533641142130825840 = ((115792089237316195423570985008687907853269984665640564039457584007913129639936 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 257 = 33596683777378021685303853810788181325470395812948041180866487919607018555656449465891780132535601725680 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 33596683777378021685303853810788181325470395812948041180866487919607018555656449465891780132535601725680 = ((6903131388249020835124862591770054686767856119082253724087669175358299890170881904182812608887337379833832 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 353 = 24459908585796463379952097533633321814860883070616562559441040779997177815307953293864553807540083975920 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 24459908585796463379952097533633321814860883070616562559441040779997177815307953293864553807540083975920 = ((8328311118657117092873331611098853895089831752258055443875236839972658037328448500830436809580621985242877 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 397 = 21748986727421036708118615691114767256034991747928580814817852381206558611596240586232210312497858044080 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 21748986727421036708118615691114767256034991747928580814817852381206558611596240586232210312497858044080 = ((5619269893133988978459608720521880296777486730409947606108622968203462472937948015540426151382489251589610 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 683 = 12641797556055858818628243674044747585133077194623201439945369539295759544368532229479044647235211776720 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 12641797556055858818628243674044747585133077194623201439945369539295759544368532229479044647235211776720 = ((7736336647767906824310446709266692609505792231090978930550942185691434881213474216489506032043094453966698 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 2113 = 4086298026874657630441595091988907998412632145730074104819066443605775564980457885818356599177306977520 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 4086298026874657630441595091988907998412632145730074104819066443605775564980457885818356599177306977520 = ((6483492461734391902668133974686441326895097482274108608504554475546235201959708275271819534499652219378884 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 65537 = 131747680406276631111022634990502503938933605809354205768995947256343802261374605379162724782361866480 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 131747680406276631111022634990502503938933605809354205768995947256343802261374605379162724782361866480 = ((6316260383478828674201144009286360002757661856304318682273731662987149483436783634965866308147251231921987 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 229153 = 37679400796787087985420616048546441026937861271411007420730635843035019261383038898614408251524743920 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 37679400796787087985420616048546441026937861271411007420730635843035019261383038898614408251524743920 = ((1433688253556065095428118542206019336447320812880079287811110557883376322230936263032272139065824496872453 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 5304641 = 1627696903670983874898054445036443107204783834368366602656558171483989919167707581480855630769669360 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 1627696903670983874898054445036443107204783834368366602656558171483989919167707581480855630769669360 = ((1192107789723888923699927162668528425774956749437052865600021101369630478567988289247983590465633136961472 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_119782433).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 119782433 = 72083589509207511030629094246003189805352273349862968499585305596013430189748337410496474838356720 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 72083589509207511030629094246003189805352273349862968499585305596013430189748337410496474838356720 = ((1453656903962913530055736355625318839951920600503584381439888765594676101095620766801727070817539086327617 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2931542417).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 2931542417 = 2945325873750149995910187244400551547825648167630673782429765673535196802442755687656893792119280 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 2945325873750149995910187244400551547825648167630673782429765673535196802442755687656893792119280 = ((1680568495656034689741469713061003531204511912541121869514267139861661279734817648298090303173887640400455 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_43872038849).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 43872038849 = 196807532936959894811454615681350246076544992164278947698072763332198693385682626102066148224240 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 196807532936959894811454615681350246076544992164278947698072763332198693385682626102066148224240 = ((3978617179884033634541959151646694589080697972497861985542452399744330463822196898567205868010525316544296 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_275509565477848842604777623828011666349761).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 - 1) / 275509565477848842604777623828011666349761 = 31339556997995988029977283785161898247419525805197063624917458160 from by norm_num]
      have h2 : (29 : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) ^ 31339556997995988029977283785161898247419525805197063624917458160 = ((4500143064250680419707064515621061044258630773254529178186591725118256655963460655125860640610981213636962 : ℕ) : ZMod 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- a odd multiple of 31: S3 with c = 5 (chains 715827883 -> 59; 715827883 -> 3033169).
theorem kill2_1_31 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 31 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 31 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g715827883 : 715827883 ∈ P := S2 715827883 prime_715827883 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 715827883 ∣ 1 + 2 ^ 31).trans ha2)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 715827883 g715827883 (by norm_num)
  have g3033169 : 3033169 ∈ P := S1 3033169 (by norm_num) (by norm_num) (hnz (by norm_num)) 715827883 g715827883 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 59 g59 3033169 g3033169 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 40: S3 with c = 17 (chains 4278255361 -> 2139127681 -> 101; 4278255361 -> 2139127681 -> 10589741).
theorem kill2_1_40 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 40 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 40 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4278255361 : 4278255361 ∈ P := S2 4278255361 prime_4278255361 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4278255361 ∣ 1 + 2 ^ 40).trans ha2)
  have g2139127681 : 2139127681 ∈ P := S1 2139127681 prime_2139127681 (by norm_num) (hnz (by norm_num)) 4278255361 g4278255361 (by norm_num)
  have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 2139127681 g2139127681 (by norm_num)
  have g10589741 : 10589741 ∈ P := S1 10589741 (by norm_num) (by norm_num) (hnz (by norm_num)) 2139127681 g2139127681 (by norm_num)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 101 g101 10589741 g10589741 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 41: S3 with c = 5 (chains 8831418697 -> 252283 -> 59; 8831418697 -> 252283 -> 1069).
theorem kill2_1_41 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 41 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 41 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8831418697 : 8831418697 ∈ P := S2 8831418697 prime_8831418697 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8831418697 ∣ 1 + 2 ^ 41).trans ha2)
  have g252283 : 252283 ∈ P := S1 252283 (by norm_num) (by norm_num) (hnz (by norm_num)) 8831418697 g8831418697 (by norm_num)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 252283 g252283 (by norm_num)
  have g1069 : 1069 ∈ P := S1 1069 (by norm_num) (by norm_num) (hnz (by norm_num)) 252283 g252283 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 59 g59 1069 g1069 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 43: S3 with c = 5 (chains 2932031007403 -> 8831418697 -> 252283 -> 59; 2932031007403 -> 8831418697 -> 252283 -> 1069).
theorem kill2_1_43 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 43 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 43 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2932031007403 : 2932031007403 ∈ P := S2 2932031007403 prime_2932031007403 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2932031007403 ∣ 1 + 2 ^ 43).trans ha2)
  have g8831418697 : 8831418697 ∈ P := S1 8831418697 prime_8831418697 (by norm_num) (hnz (by norm_num)) 2932031007403 g2932031007403 (by norm_num)
  have g252283 : 252283 ∈ P := S1 252283 (by norm_num) (by norm_num) (hnz (by norm_num)) 8831418697 g8831418697 (by norm_num)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 252283 g252283 (by norm_num)
  have g1069 : 1069 ∈ P := S1 1069 (by norm_num) (by norm_num) (hnz (by norm_num)) 252283 g252283 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 59 g59 1069 g1069 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 44: S3 with c = 23 (chains 2931542417; 2931542417 -> 367).
theorem kill2_1_44 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 44 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 44 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2931542417 : 2931542417 ∈ P := S2 2931542417 prime_2931542417 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2931542417 ∣ 1 + 2 ^ 44).trans ha2)
  have g367 : 367 ∈ P := S1 367 (by norm_num) (by norm_num) (hnz (by norm_num)) 2931542417 g2931542417 (by norm_num)
  have := S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 2931542417 g2931542417 367 g367 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 47: S6 with c = 7 (chains 165768537521).
theorem kill2_1_47 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 47 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 47 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g165768537521 : 165768537521 ∈ P := S2 165768537521 prime_165768537521 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 165768537521 ∣ 1 + 2 ^ 47).trans ha2)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 165768537521 g165768537521 (by norm_num)

-- a odd multiple of 49: S6 with c = 19 (chains 4363953127297).
theorem kill2_1_49 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 49 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 49 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4363953127297 : 4363953127297 ∈ P := S2 4363953127297 prime_4363953127297 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4363953127297 ∣ 1 + 2 ^ 49).trans ha2)
  exact S6 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 4363953127297 g4363953127297 (by norm_num)

-- a odd multiple of 53: S3 with c = 5 (chains 28059810762433 -> 1275445943747 -> 29; 28059810762433 -> 1275445943747 -> 1221691517 -> 22623917 -> 139).
theorem kill2_1_53 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 53 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 53 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g28059810762433 : 28059810762433 ∈ P := S2 28059810762433 prime_28059810762433 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 28059810762433 ∣ 1 + 2 ^ 53).trans ha2)
  have g1275445943747 : 1275445943747 ∈ P := S1 1275445943747 prime_1275445943747 (by norm_num) (hnz (by norm_num)) 28059810762433 g28059810762433 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 1275445943747 g1275445943747 (by norm_num)
  have g1221691517 : 1221691517 ∈ P := S1 1221691517 prime_1221691517 (by norm_num) (hnz (by norm_num)) 1275445943747 g1275445943747 (by norm_num)
  have g22623917 : 22623917 ∈ P := S1 22623917 (by norm_num) (by norm_num) (hnz (by norm_num)) 1221691517 g1221691517 (by norm_num)
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 22623917 g22623917 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 139 g139 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 58: S4 with c = 5 (chains 107367629).
theorem kill2_1_58 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 58 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 58 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g107367629 : 107367629 ∈ P := S2 107367629 prime_107367629 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 107367629 ∣ 1 + 2 ^ 58).trans ha2)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 2 ^ 58).trans ha2) 107367629 g107367629 (by norm_num)

-- a odd multiple of 61: S6 with c = 5 (chains 768614336404564651 -> 37171 -> 9293 -> 1549).
theorem kill2_1_61 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 61 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 61 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g768614336404564651 : 768614336404564651 ∈ P := S2 768614336404564651 prime_768614336404564651 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 768614336404564651 ∣ 1 + 2 ^ 61).trans ha2)
  have g37171 : 37171 ∈ P := S1 37171 (by norm_num) (by norm_num) (hnz (by norm_num)) 768614336404564651 g768614336404564651 (by norm_num)
  have g9293 : 9293 ∈ P := S1 9293 (by norm_num) (by norm_num) (hnz (by norm_num)) 37171 g37171 (by norm_num)
  have g1549 : 1549 ∈ P := S1 1549 (by norm_num) (by norm_num) (hnz (by norm_num)) 9293 g9293 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1549 g1549 (by norm_num)

-- a odd multiple of 71: S3 with c = 11 (chains 56409643 -> 14102411 -> 131; 56409643 -> 14102411 -> 8971 -> 2243).
theorem kill2_1_71 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 71 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 71 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g56409643 : 56409643 ∈ P := S2 56409643 prime_56409643 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 56409643 ∣ 1 + 2 ^ 71).trans ha2)
  have g14102411 : 14102411 ∈ P := S1 14102411 (by norm_num) (by norm_num) (hnz (by norm_num)) 56409643 g56409643 (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 14102411 g14102411 (by norm_num)
  have g8971 : 8971 ∈ P := S1 8971 (by norm_num) (by norm_num) (hnz (by norm_num)) 14102411 g14102411 (by norm_num)
  have g2243 : 2243 ∈ P := S1 2243 (by norm_num) (by norm_num) (hnz (by norm_num)) 8971 g8971 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 131 g131 2243 g2243 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 73: S3 with c = 5 (chains 1753 -> 877 -> 439; 1795918038741070627 -> 448979509685267657 -> 24943306093625981 -> 151 -> 19).
theorem kill2_1_73 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 73 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 73 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1753 : 1753 ∈ P := S2 1753 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1753 ∣ 1 + 2 ^ 73).trans ha2)
  have g877 : 877 ∈ P := S1 877 (by norm_num) (by norm_num) (hnz (by norm_num)) 1753 g1753 (by norm_num)
  have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 877 g877 (by norm_num)
  have g1795918038741070627 : 1795918038741070627 ∈ P := S2 1795918038741070627 prime_1795918038741070627 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1795918038741070627 ∣ 1 + 2 ^ 73).trans ha2)
  have g448979509685267657 : 448979509685267657 ∈ P := S1 448979509685267657 prime_448979509685267657 (by norm_num) (hnz (by norm_num)) 1795918038741070627 g1795918038741070627 (by norm_num)
  have g24943306093625981 : 24943306093625981 ∈ P := S1 24943306093625981 prime_24943306093625981 (by norm_num) (hnz (by norm_num)) 448979509685267657 g448979509685267657 (by norm_num)
  have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 24943306093625981 g24943306093625981 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 g151 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 439 g439 19 g19 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 79: S3 with c = 13 (chains 201487636602438195784363 -> 617 -> 103; 201487636602438195784363 -> 78233).
theorem kill2_1_79 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 79 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 79 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g201487636602438195784363 : 201487636602438195784363 ∈ P := S2 201487636602438195784363 prime_201487636602438195784363 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 201487636602438195784363 ∣ 1 + 2 ^ 79).trans ha2)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 201487636602438195784363 g201487636602438195784363 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g78233 : 78233 ∈ P := S1 78233 (by norm_num) (by norm_num) (hnz (by norm_num)) 201487636602438195784363 g201487636602438195784363 (by norm_num)
  have := S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 78233 g78233 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 88: S3 with c = 43 (chains 257; 119782433).
theorem kill2_1_88 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 88 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 88 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 257 ∣ 1 + 2 ^ 88).trans ha2)
  have g119782433 : 119782433 ∈ P := S2 119782433 prime_119782433 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 119782433 ∣ 1 + 2 ^ 88).trans ha2)
  have := S3 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 119782433 g119782433 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 89: S3 with c = 5 (chains 179; 62020897 -> 2459).
theorem kill2_1_89 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 89 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 89 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g179 : 179 ∈ P := S2 179 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 179 ∣ 1 + 2 ^ 89).trans ha2)
  have g62020897 : 62020897 ∈ P := S2 62020897 prime_62020897 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 62020897 ∣ 1 + 2 ^ 89).trans ha2)
  have g2459 : 2459 ∈ P := S1 2459 (by norm_num) (by norm_num) (hnz (by norm_num)) 62020897 g62020897 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 179 g179 2459 g2459 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 92: S3 with c = 11 (chains 291280009243618888211558641; 291280009243618888211558641 -> 97591777 -> 48795889).
theorem kill2_1_92 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 92 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 92 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g291280009243618888211558641 : 291280009243618888211558641 ∈ P := S2 291280009243618888211558641 prime_291280009243618888211558641 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 291280009243618888211558641 ∣ 1 + 2 ^ 92).trans ha2)
  have g97591777 : 97591777 ∈ P := S1 97591777 prime_97591777 (by norm_num) (hnz (by norm_num)) 291280009243618888211558641 g291280009243618888211558641 (by norm_num)
  have g48795889 : 48795889 ∈ P := S1 48795889 prime_48795889 (by norm_num) (hnz (by norm_num)) 97591777 g97591777 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 291280009243618888211558641 g291280009243618888211558641 48795889 g48795889 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 93: S3 with c = 7 (chains 529510939; 529510939 -> 193 -> 97).
theorem kill2_1_93 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 93 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 93 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g529510939 : 529510939 ∈ P := S2 529510939 prime_529510939 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 529510939 ∣ 1 + 2 ^ 93).trans ha2)
  have g193 : 193 ∈ P := S1 193 (by norm_num) (by norm_num) (hnz (by norm_num)) 529510939 g529510939 (by norm_num)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 193 g193 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 529510939 g529510939 97 g97 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 101: S3 with c = 19 (chains 845100400152152934331135470251; 845100400152152934331135470251 -> 683).
theorem kill2_1_101 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 101 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 101 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g845100400152152934331135470251 : 845100400152152934331135470251 ∈ P := S2 845100400152152934331135470251 prime_845100400152152934331135470251 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 845100400152152934331135470251 ∣ 1 + 2 ^ 101).trans ha2)
  have g683 : 683 ∈ P := S1 683 (by norm_num) (by norm_num) (hnz (by norm_num)) 845100400152152934331135470251 g845100400152152934331135470251 (by norm_num)
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 845100400152152934331135470251 g845100400152152934331135470251 683 g683 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 103: S3 with c = 5 (chains 415141630193 -> 974510869; 415141630193 -> 974510869 -> 862399).
theorem kill2_1_103 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 103 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 103 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g415141630193 : 415141630193 ∈ P := S2 415141630193 prime_415141630193 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 415141630193 ∣ 1 + 2 ^ 103).trans ha2)
  have g974510869 : 974510869 ∈ P := S1 974510869 prime_974510869 (by norm_num) (hnz (by norm_num)) 415141630193 g415141630193 (by norm_num)
  have g862399 : 862399 ∈ P := S1 862399 (by norm_num) (by norm_num) (hnz (by norm_num)) 974510869 g974510869 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 974510869 g974510869 862399 g862399 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 104: S3 with c = 11 (chains 78919881726271091143763623681 -> 39459940863135545571881811841 -> 19729970431567772785940905921 -> 9864985215783886392970452961; 78919881726271091143763623681 -> 39459940863135545571881811841 -> 19729970431567772785940905921 -> 9864985215783886392970452961 -> 18457).
theorem kill2_1_104 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 104 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 104 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g78919881726271091143763623681 : 78919881726271091143763623681 ∈ P := S2 78919881726271091143763623681 prime_78919881726271091143763623681 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 78919881726271091143763623681 ∣ 1 + 2 ^ 104).trans ha2)
  have g39459940863135545571881811841 : 39459940863135545571881811841 ∈ P := S1 39459940863135545571881811841 prime_39459940863135545571881811841 (by norm_num) (hnz (by norm_num)) 78919881726271091143763623681 g78919881726271091143763623681 (by norm_num)
  have g19729970431567772785940905921 : 19729970431567772785940905921 ∈ P := S1 19729970431567772785940905921 prime_19729970431567772785940905921 (by norm_num) (hnz (by norm_num)) 39459940863135545571881811841 g39459940863135545571881811841 (by norm_num)
  have g9864985215783886392970452961 : 9864985215783886392970452961 ∈ P := S1 9864985215783886392970452961 prime_9864985215783886392970452961 (by norm_num) (hnz (by norm_num)) 19729970431567772785940905921 g19729970431567772785940905921 (by norm_num)
  have g18457 : 18457 ∈ P := S1 18457 (by norm_num) (by norm_num) (hnz (by norm_num)) 9864985215783886392970452961 g9864985215783886392970452961 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 9864985215783886392970452961 g9864985215783886392970452961 18457 g18457 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 107: S3 with c = 7 (chains 643; 84115747449047881488635567801 -> 13).
theorem kill2_1_107 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 107 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 107 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g643 : 643 ∈ P := S2 643 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 643 ∣ 1 + 2 ^ 107).trans ha2)
  have g84115747449047881488635567801 : 84115747449047881488635567801 ∈ P := S2 84115747449047881488635567801 prime_84115747449047881488635567801 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 84115747449047881488635567801 ∣ 1 + 2 ^ 107).trans ha2)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 84115747449047881488635567801 g84115747449047881488635567801 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 643 g643 13 g13 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 109: S6 with c = 5 (chains 104124649).
theorem kill2_1_109 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 109 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 109 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g104124649 : 104124649 ∈ P := S2 104124649 prime_104124649 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 104124649 ∣ 1 + 2 ^ 109).trans ha2)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 104124649 g104124649 (by norm_num)

-- a odd multiple of 113: S3 with c = 7 (chains 48817; 636190001).
theorem kill2_1_113 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 113 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 113 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g48817 : 48817 ∈ P := S2 48817 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 48817 ∣ 1 + 2 ^ 113).trans ha2)
  have g636190001 : 636190001 ∈ P := S2 636190001 prime_636190001 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 636190001 ∣ 1 + 2 ^ 113).trans ha2)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 48817 g48817 636190001 g636190001 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 127: S6 with c = 13 (chains 56713727820156410577229101238628035243 -> 4051 -> 1013).
theorem kill2_1_127 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 127 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 127 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g56713727820156410577229101238628035243 : 56713727820156410577229101238628035243 ∈ P := S2 56713727820156410577229101238628035243 prime_56713727820156410577229101238628035243 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 56713727820156410577229101238628035243 ∣ 1 + 2 ^ 127).trans ha2)
  have g4051 : 4051 ∈ P := S1 4051 (by norm_num) (by norm_num) (hnz (by norm_num)) 56713727820156410577229101238628035243 g56713727820156410577229101238628035243 (by norm_num)
  have g1013 : 1013 ∈ P := S1 1013 (by norm_num) (by norm_num) (hnz (by norm_num)) 4051 g4051 (by norm_num)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1013 g1013 (by norm_num)

-- a odd multiple of 128: S3 with c = 23 (chains 59649589127497217 -> 733 -> 367; 59649589127497217 -> 13562889751591 -> 1440437 -> 240073).
theorem kill2_1_128 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 128 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 128 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g59649589127497217 : 59649589127497217 ∈ P := S2 59649589127497217 prime_59649589127497217 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 59649589127497217 ∣ 1 + 2 ^ 128).trans ha2)
  have g733 : 733 ∈ P := S1 733 (by norm_num) (by norm_num) (hnz (by norm_num)) 59649589127497217 g59649589127497217 (by norm_num)
  have g367 : 367 ∈ P := S1 367 (by norm_num) (by norm_num) (hnz (by norm_num)) 733 g733 (by norm_num)
  have g13562889751591 : 13562889751591 ∈ P := S1 13562889751591 prime_13562889751591 (by norm_num) (hnz (by norm_num)) 59649589127497217 g59649589127497217 (by norm_num)
  have g1440437 : 1440437 ∈ P := S1 1440437 (by norm_num) (by norm_num) (hnz (by norm_num)) 13562889751591 g13562889751591 (by norm_num)
  have g240073 : 240073 ∈ P := S1 240073 (by norm_num) (by norm_num) (hnz (by norm_num)) 1440437 g1440437 (by norm_num)
  have := S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 367 g367 240073 g240073 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 129: S3 with c = 5 (chains 1591582393 -> 419; 1591582393 -> 1899263 -> 2473 -> 1237 -> 619).
theorem kill2_1_129 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 129 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 129 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1591582393 : 1591582393 ∈ P := S2 1591582393 prime_1591582393 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1591582393 ∣ 1 + 2 ^ 129).trans ha2)
  have g419 : 419 ∈ P := S1 419 (by norm_num) (by norm_num) (hnz (by norm_num)) 1591582393 g1591582393 (by norm_num)
  have g1899263 : 1899263 ∈ P := S1 1899263 (by norm_num) (by norm_num) (hnz (by norm_num)) 1591582393 g1591582393 (by norm_num)
  have g2473 : 2473 ∈ P := S1 2473 (by norm_num) (by norm_num) (hnz (by norm_num)) 1899263 g1899263 (by norm_num)
  have g1237 : 1237 ∈ P := S1 1237 (by norm_num) (by norm_num) (hnz (by norm_num)) 2473 g2473 (by norm_num)
  have g619 : 619 ∈ P := S1 619 (by norm_num) (by norm_num) (hnz (by norm_num)) 1237 g1237 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 419 g419 619 g619 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 136: S3 with c = 11 (chains 257 -> 43; 2368179743873 -> 4441 -> 2221).
theorem kill2_1_136 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 136 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 136 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 257 ∣ 1 + 2 ^ 136).trans ha2)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
  have g2368179743873 : 2368179743873 ∈ P := S2 2368179743873 prime_2368179743873 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2368179743873 ∣ 1 + 2 ^ 136).trans ha2)
  have g4441 : 4441 ∈ P := S1 4441 (by norm_num) (by norm_num) (hnz (by norm_num)) 2368179743873 g2368179743873 (by norm_num)
  have g2221 : 2221 ∈ P := S1 2221 (by norm_num) (by norm_num) (hnz (by norm_num)) 4441 g4441 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 2221 g2221 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 137: S6 with c = 5 (chains 32127963626435681 -> 2399).
theorem kill2_1_137 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 137 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 137 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g32127963626435681 : 32127963626435681 ∈ P := S2 32127963626435681 prime_32127963626435681 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 32127963626435681 ∣ 1 + 2 ^ 137).trans ha2)
  have g2399 : 2399 ∈ P := S1 2399 (by norm_num) (by norm_num) (hnz (by norm_num)) 32127963626435681 g32127963626435681 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2399 g2399 (by norm_num)

-- a odd multiple of 139: S6 with c = 5 (chains 51542639524661795300074174250365699).
theorem kill2_1_139 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 139 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 139 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g51542639524661795300074174250365699 : 51542639524661795300074174250365699 ∈ P := S2 51542639524661795300074174250365699 prime_51542639524661795300074174250365699 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 51542639524661795300074174250365699 ∣ 1 + 2 ^ 139).trans ha2)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 51542639524661795300074174250365699 g51542639524661795300074174250365699 (by norm_num)

-- a odd multiple of 148: S6 with c = 5 (chains 20988936657440586486151264256610222593863921 -> 212480658612043 -> 4192399).
theorem kill2_1_148 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 148 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 148 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g20988936657440586486151264256610222593863921 : 20988936657440586486151264256610222593863921 ∈ P := S2 20988936657440586486151264256610222593863921 prime_20988936657440586486151264256610222593863921 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 20988936657440586486151264256610222593863921 ∣ 1 + 2 ^ 148).trans ha2)
  have g212480658612043 : 212480658612043 ∈ P := S1 212480658612043 prime_212480658612043 (by norm_num) (hnz (by norm_num)) 20988936657440586486151264256610222593863921 g20988936657440586486151264256610222593863921 (by norm_num)
  have g4192399 : 4192399 ∈ P := S1 4192399 (by norm_num) (by norm_num) (hnz (by norm_num)) 212480658612043 g212480658612043 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4192399 g4192399 (by norm_num)

-- a odd multiple of 151: S6 with c = 7 (chains 18717738334417 -> 2351).
theorem kill2_1_151 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 151 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 151 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g18717738334417 : 18717738334417 ∈ P := S2 18717738334417 prime_18717738334417 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 18717738334417 ∣ 1 + 2 ^ 151).trans ha2)
  have g2351 : 2351 ∈ P := S1 2351 (by norm_num) (by norm_num) (hnz (by norm_num)) 18717738334417 g18717738334417 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 2351 g2351 (by norm_num)

-- a odd multiple of 159: S3 with c = 5 (chains 28059810762433 -> 1275445943747 -> 29; 28059810762433 -> 1275445943747 -> 1221691517 -> 22623917 -> 139).
theorem kill2_1_159 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 159 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 159 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g28059810762433 : 28059810762433 ∈ P := S2 28059810762433 prime_28059810762433 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 28059810762433 ∣ 1 + 2 ^ 159).trans ha2)
  have g1275445943747 : 1275445943747 ∈ P := S1 1275445943747 prime_1275445943747 (by norm_num) (hnz (by norm_num)) 28059810762433 g28059810762433 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 1275445943747 g1275445943747 (by norm_num)
  have g1221691517 : 1221691517 ∈ P := S1 1221691517 prime_1221691517 (by norm_num) (hnz (by norm_num)) 1275445943747 g1275445943747 (by norm_num)
  have g22623917 : 22623917 ∈ P := S1 22623917 (by norm_num) (by norm_num) (hnz (by norm_num)) 1221691517 g1221691517 (by norm_num)
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 22623917 g22623917 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 139 g139 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 161: S4 with c = 43 (chains 2796203).
theorem kill2_1_161 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 161 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 161 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2796203 : 2796203 ∈ P := S2 2796203 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2796203 ∣ 1 + 2 ^ 161).trans ha2)
  exact S4 43 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 43 ∣ 1 + 2 ^ 161).trans ha2) 2796203 g2796203 (by norm_num)

-- a odd multiple of 163: S3 with c = 7 (chains 11281292593 -> 13; 11281292593 -> 419).
theorem kill2_1_163 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 163 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 163 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g11281292593 : 11281292593 ∈ P := S2 11281292593 prime_11281292593 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 11281292593 ∣ 1 + 2 ^ 163).trans ha2)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 11281292593 g11281292593 (by norm_num)
  have g419 : 419 ∈ P := S1 419 (by norm_num) (by norm_num) (hnz (by norm_num)) 11281292593 g11281292593 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 419 g419 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 164: S6 with c = 19 (chains 8562191377 -> 1438057 -> 8663).
theorem kill2_1_164 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 164 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 164 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8562191377 : 8562191377 ∈ P := S2 8562191377 prime_8562191377 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8562191377 ∣ 1 + 2 ^ 164).trans ha2)
  have g1438057 : 1438057 ∈ P := S1 1438057 (by norm_num) (by norm_num) (hnz (by norm_num)) 8562191377 g8562191377 (by norm_num)
  have g8663 : 8663 ∈ P := S1 8663 (by norm_num) (by norm_num) (hnz (by norm_num)) 1438057 g1438057 (by norm_num)
  exact S6 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 8663 g8663 (by norm_num)

-- a odd multiple of 166: S4 with c = 5 (chains 997 -> 499).
theorem kill2_1_166 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 166 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 166 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g997 : 997 ∈ P := S2 997 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 997 ∣ 1 + 2 ^ 166).trans ha2)
  have g499 : 499 ∈ P := S1 499 (by norm_num) (by norm_num) (hnz (by norm_num)) 997 g997 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 2 ^ 166).trans ha2) 499 g499 (by norm_num)

-- a odd multiple of 167: S6 with c = 11 (chains 62357403192785191176690552862561408838653121833643).
theorem kill2_1_167 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 167 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 167 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g62357403192785191176690552862561408838653121833643 : 62357403192785191176690552862561408838653121833643 ∈ P := S2 62357403192785191176690552862561408838653121833643 prime_62357403192785191176690552862561408838653121833643 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 62357403192785191176690552862561408838653121833643 ∣ 1 + 2 ^ 167).trans ha2)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 62357403192785191176690552862561408838653121833643 g62357403192785191176690552862561408838653121833643 (by norm_num)

-- a odd multiple of 172: S4 with c = 17 (chains 3855260977 -> 517207).
theorem kill2_1_172 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 172 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 172 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3855260977 : 3855260977 ∈ P := S2 3855260977 prime_3855260977 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3855260977 ∣ 1 + 2 ^ 172).trans ha2)
  have g517207 : 517207 ∈ P := S1 517207 (by norm_num) (by norm_num) (hnz (by norm_num)) 3855260977 g3855260977 (by norm_num)
  exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 17 ∣ 1 + 2 ^ 172).trans ha2) 517207 g517207 (by norm_num)

-- a odd multiple of 173: S6 with c = 7 (chains 35374479827 -> 2947873319).
theorem kill2_1_173 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 173 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 173 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g35374479827 : 35374479827 ∈ P := S2 35374479827 prime_35374479827 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 35374479827 ∣ 1 + 2 ^ 173).trans ha2)
  have g2947873319 : 2947873319 ∈ P := S1 2947873319 prime_2947873319 (by norm_num) (hnz (by norm_num)) 35374479827 g35374479827 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 2947873319 g2947873319 (by norm_num)

-- a odd multiple of 174: S4 with c = 5 (chains 349).
theorem kill2_1_174 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 174 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 174 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g349 : 349 ∈ P := S2 349 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 349 ∣ 1 + 2 ^ 174).trans ha2)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 2 ^ 174).trans ha2) 349 g349 (by norm_num)

-- a odd multiple of 176: S6 with c = 7 (chains 5304641).
theorem kill2_1_176 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 176 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 176 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5304641 : 5304641 ∈ P := S2 5304641 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5304641 ∣ 1 + 2 ^ 176).trans ha2)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 5304641 g5304641 (by norm_num)

-- a odd multiple of 178: S4 with c = 5 (chains 1069).
theorem kill2_1_178 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 178 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 178 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1069 : 1069 ∈ P := S2 1069 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1069 ∣ 1 + 2 ^ 178).trans ha2)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 2 ^ 178).trans ha2) 1069 g1069 (by norm_num)

-- a odd multiple of 179: S6 with c = 5 (chains 58745093521 -> 126457 -> 1193 -> 199).
theorem kill2_1_179 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 179 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 179 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g58745093521 : 58745093521 ∈ P := S2 58745093521 prime_58745093521 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 58745093521 ∣ 1 + 2 ^ 179).trans ha2)
  have g126457 : 126457 ∈ P := S1 126457 (by norm_num) (by norm_num) (hnz (by norm_num)) 58745093521 g58745093521 (by norm_num)
  have g1193 : 1193 ∈ P := S1 1193 (by norm_num) (by norm_num) (hnz (by norm_num)) 126457 g126457 (by norm_num)
  have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 1193 g1193 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)

-- a odd multiple of 181: S6 with c = 7 (chains 31675363).
theorem kill2_1_181 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 181 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 181 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g31675363 : 31675363 ∈ P := S2 31675363 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 31675363 ∣ 1 + 2 ^ 181).trans ha2)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 31675363 g31675363 (by norm_num)

-- a odd multiple of 183: S6 with c = 5 (chains 768614336404564651 -> 37171 -> 9293 -> 1549).
theorem kill2_1_183 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 183 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 183 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g768614336404564651 : 768614336404564651 ∈ P := S2 768614336404564651 prime_768614336404564651 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 768614336404564651 ∣ 1 + 2 ^ 183).trans ha2)
  have g37171 : 37171 ∈ P := S1 37171 (by norm_num) (by norm_num) (hnz (by norm_num)) 768614336404564651 g768614336404564651 (by norm_num)
  have g9293 : 9293 ∈ P := S1 9293 (by norm_num) (by norm_num) (hnz (by norm_num)) 37171 g37171 (by norm_num)
  have g1549 : 1549 ∈ P := S1 1549 (by norm_num) (by norm_num) (hnz (by norm_num)) 9293 g9293 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1549 g1549 (by norm_num)

-- a odd multiple of 184: S3 with c = 17 (chains 43717618369; 43717618369 -> 937 -> 67).
theorem kill2_1_184 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 184 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 184 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43717618369 : 43717618369 ∈ P := S2 43717618369 prime_43717618369 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43717618369 ∣ 1 + 2 ^ 184).trans ha2)
  have g937 : 937 ∈ P := S1 937 (by norm_num) (by norm_num) (hnz (by norm_num)) 43717618369 g43717618369 (by norm_num)
  have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 937 g937 (by norm_num)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 43717618369 g43717618369 67 g67 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 187: S3 with c = 5 (chains 683 -> 19; 2191165825376888084750157716424579062015865776131 -> 14231135141929).
theorem kill2_1_187 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 187 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 187 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g683 : 683 ∈ P := S2 683 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 683 ∣ 1 + 2 ^ 187).trans ha2)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 683 g683 (by norm_num)
  have g2191165825376888084750157716424579062015865776131 : 2191165825376888084750157716424579062015865776131 ∈ P := S2 2191165825376888084750157716424579062015865776131 prime_2191165825376888084750157716424579062015865776131 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2191165825376888084750157716424579062015865776131 ∣ 1 + 2 ^ 187).trans ha2)
  have g14231135141929 : 14231135141929 ∈ P := S1 14231135141929 prime_14231135141929 (by norm_num) (hnz (by norm_num)) 2191165825376888084750157716424579062015865776131 g2191165825376888084750157716424579062015865776131 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 14231135141929 g14231135141929 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 188: S3 with c = 5 (chains 1198107457 -> 599053729; 1198107457 -> 599053729 -> 16453 -> 19).
theorem kill2_1_188 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 188 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 188 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1198107457 : 1198107457 ∈ P := S2 1198107457 prime_1198107457 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1198107457 ∣ 1 + 2 ^ 188).trans ha2)
  have g599053729 : 599053729 ∈ P := S1 599053729 prime_599053729 (by norm_num) (hnz (by norm_num)) 1198107457 g1198107457 (by norm_num)
  have g16453 : 16453 ∈ P := S1 16453 (by norm_num) (by norm_num) (hnz (by norm_num)) 599053729 g599053729 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 16453 g16453 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 599053729 g599053729 19 g19 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 191: S3 with c = 19 (chains 1046183622564446793972631570534611069350392574077339085483; 1046183622564446793972631570534611069350392574077339085483 -> 379).
theorem kill2_1_191 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 191 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 191 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1046183622564446793972631570534611069350392574077339085483 : 1046183622564446793972631570534611069350392574077339085483 ∈ P := S2 1046183622564446793972631570534611069350392574077339085483 prime_1046183622564446793972631570534611069350392574077339085483 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1046183622564446793972631570534611069350392574077339085483 ∣ 1 + 2 ^ 191).trans ha2)
  have g379 : 379 ∈ P := S1 379 (by norm_num) (by norm_num) (hnz (by norm_num)) 1046183622564446793972631570534611069350392574077339085483 g1046183622564446793972631570534611069350392574077339085483 (by norm_num)
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 1046183622564446793972631570534611069350392574077339085483 g1046183622564446793972631570534611069350392574077339085483 379 g379 (by norm_num) (by norm_num)
  omega

-- a odd multiple of 193: S6 with c = 23 (chains 1871670769).
theorem kill2_1_193 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 193 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 193 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1871670769 : 1871670769 ∈ P := S2 1871670769 prime_1871670769 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1871670769 ∣ 1 + 2 ^ 193).trans ha2)
  exact S6 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 1871670769 g1871670769 (by norm_num)

-- a odd multiple of 194: S4 with c = 5 (chains 389).
theorem kill2_1_194 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 194 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 194 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g389 : 389 ∈ P := S2 389 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 389 ∣ 1 + 2 ^ 194).trans ha2)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 2 ^ 194).trans ha2) 389 g389 (by norm_num)

-- a odd multiple of 197: S6 with c = 5 (chains 197002597249).
theorem kill2_1_197 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 197 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 197 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g197002597249 : 197002597249 ∈ P := S2 197002597249 prime_197002597249 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 197002597249 ∣ 1 + 2 ^ 197).trans ha2)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 197002597249 g197002597249 (by norm_num)

-- a odd multiple of 199: S6 with c = 5 (chains 267823007376498379256993682056860433753700498963798805883563 -> 197002597249).
theorem kill2_1_199 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 199 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 199 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g267823007376498379256993682056860433753700498963798805883563 : 267823007376498379256993682056860433753700498963798805883563 ∈ P := S2 267823007376498379256993682056860433753700498963798805883563 prime_267823007376498379256993682056860433753700498963798805883563 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 267823007376498379256993682056860433753700498963798805883563 ∣ 1 + 2 ^ 199).trans ha2)
  have g197002597249 : 197002597249 ∈ P := S1 197002597249 prime_197002597249 (by norm_num) (hnz (by norm_num)) 267823007376498379256993682056860433753700498963798805883563 g267823007376498379256993682056860433753700498963798805883563 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 197002597249 g197002597249 (by norm_num)

-- a odd multiple of 200: S6 with c = 5 (chains 82471201 -> 149).
theorem kill2_1_200 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 200 ∣ 1 + 2 ^ m) : False := by
  have ha2 : 1 + 2 ^ 200 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g82471201 : 82471201 ∈ P := S2 82471201 prime_82471201 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 82471201 ∣ 1 + 2 ^ 200).trans ha2)
  have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 82471201 g82471201 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)

-- a odd multiple of 2 and e odd multiple of 2: KA with c = 5 (chains none).
theorem kill2_2_2 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 2 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 2 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S_sq hP hK E (c := 5) (by norm_num) (by norm_num) (hnz (by norm_num))
    ((mul_dvd_mul ((by norm_num : 5 ∣ 1 + 2 ^ 2).trans ha2) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd)).mul_right _)

-- a odd multiple of 6 and e odd multiple of 2: KA with c = 5 (chains none).
theorem kill2_2_6 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 6 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 6 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S_sq hP hK E (c := 5) (by norm_num) (by norm_num) (hnz (by norm_num))
    ((mul_dvd_mul ((by norm_num : 5 ∣ 1 + 2 ^ 6).trans ha2) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd)).mul_right _)

-- a odd multiple of 9 and e odd multiple of 2: S8 with c = 5 (chains 19).
theorem kill2_2_9 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 9 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 9 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g19 : 19 ∈ P := S2 19 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 19 ∣ 1 + 2 ^ 9).trans ha2)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd) 19 g19 (by norm_num)

-- a odd multiple of 11 and e odd multiple of 2: S8 with c = 5 (chains 683 -> 19).
theorem kill2_2_11 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 11 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 11 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g683 : 683 ∈ P := S2 683 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 683 ∣ 1 + 2 ^ 11).trans ha2)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 683 g683 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd) 19 g19 (by norm_num)

-- a odd multiple of 13 and e odd multiple of 2: S8 with c = 5 (chains 2731 -> 683 -> 19).
theorem kill2_2_13 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 13 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 13 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2731 : 2731 ∈ P := S2 2731 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2731 ∣ 1 + 2 ^ 13).trans ha2)
  have g683 : 683 ∈ P := S1 683 (by norm_num) (by norm_num) (hnz (by norm_num)) 2731 g2731 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 683 g683 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd) 19 g19 (by norm_num)

-- a odd multiple of 21 and e odd multiple of 2: S8 with c = 5 (chains 5419).
theorem kill2_2_21 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 21 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 21 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5419 : 5419 ∈ P := S2 5419 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5419 ∣ 1 + 2 ^ 21).trans ha2)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd) 5419 g5419 (by norm_num)

-- a odd multiple of 23 and e odd multiple of 2: S8 with c = 5 (chains 2796203 -> 5419).
theorem kill2_2_23 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 23 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 23 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2796203 : 2796203 ∈ P := S2 2796203 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2796203 ∣ 1 + 2 ^ 23).trans ha2)
  have g5419 : 5419 ∈ P := S1 5419 (by norm_num) (by norm_num) (hnz (by norm_num)) 2796203 g2796203 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd) 5419 g5419 (by norm_num)

-- a odd multiple of 158 and e odd multiple of 2: KA with c = 5 (chains none).
theorem kill2_2_158 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 158 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 158 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S_sq hP hK E (c := 5) (by norm_num) (by norm_num) (hnz (by norm_num))
    ((mul_dvd_mul ((by norm_num : 5 ∣ 1 + 2 ^ 158).trans ha2) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd)).mul_right _)

-- a odd multiple of 169 and e odd multiple of 2: S8 with c = 5 (chains 2731 -> 683 -> 19).
theorem kill2_2_169 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 169 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 169 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2731 : 2731 ∈ P := S2 2731 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2731 ∣ 1 + 2 ^ 169).trans ha2)
  have g683 : 683 ∈ P := S1 683 (by norm_num) (by norm_num) (hnz (by norm_num)) 2731 g2731 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 683 g683 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd) 19 g19 (by norm_num)

-- a odd multiple of 219 and e odd multiple of 2: S8 with c = 5 (chains 1753 -> 877 -> 439).
theorem kill2_2_219 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 219 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 219 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1753 : 1753 ∈ P := S2 1753 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1753 ∣ 1 + 2 ^ 219).trans ha2)
  have g877 : 877 ∈ P := S1 877 (by norm_num) (by norm_num) (hnz (by norm_num)) 1753 g1753 (by norm_num)
  have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 877 g877 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd) 439 g439 (by norm_num)

-- a odd multiple of 272 and e odd multiple of 2: S8 with c = 5 (chains 5441 -> 907 -> 227 -> 19).
theorem kill2_2_272 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 272 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 272 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5441 : 5441 ∈ P := S2 5441 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 272 = 2 ^ 200 * 2 ^ 72 by rw [← pow_add]]; norm_num : 5441 ∣ 1 + 2 ^ 272).trans ha2)
  have g907 : 907 ∈ P := S1 907 (by norm_num) (by norm_num) (hnz (by norm_num)) 5441 g5441 (by norm_num)
  have g227 : 227 ∈ P := S1 227 (by norm_num) (by norm_num) (hnz (by norm_num)) 907 g907 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 227 g227 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd) 19 g19 (by norm_num)

-- a odd multiple of 302 and e odd multiple of 2: KA with c = 5 (chains none).
theorem kill2_2_302 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 302 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 302 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S_sq hP hK E (c := 5) (by norm_num) (by norm_num) (hnz (by norm_num))
    ((mul_dvd_mul ((by rw [show (2:ℕ) ^ 302 = 2 ^ 200 * 2 ^ 102 by rw [← pow_add]]; norm_num : 5 ∣ 1 + 2 ^ 302).trans ha2) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd)).mul_right _)

-- a odd multiple of 332 and e odd multiple of 2: S8 with c = 5 (chains 11953 -> 139).
theorem kill2_2_332 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 332 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 332 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g11953 : 11953 ∈ P := S2 11953 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 332 = 2 ^ 200 * 2 ^ 132 by rw [← pow_add]]; norm_num : 11953 ∣ 1 + 2 ^ 332).trans ha2)
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 11953 g11953 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd) 139 g139 (by norm_num)

-- a odd multiple of 356 and e odd multiple of 2: S8 with c = 5 (chains 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 -> 2339).
theorem kill2_2_356 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 356 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 356 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 : 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 ∈ P := S2 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 prime_8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 356 = 2 ^ 200 * 2 ^ 156 by rw [← pow_add]]; norm_num : 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 ∣ 1 + 2 ^ 356).trans ha2)
  have g2339 : 2339 ∈ P := S1 2339 (by norm_num) (by norm_num) (hnz (by norm_num)) 8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 g8634347730786151573123090429372562600645891723927646583482687395339003768803707512734187494061649643499761 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd) 2339 g2339 (by norm_num)

-- a odd multiple of 373 and e odd multiple of 2: S8 with c = 5 (chains 60427 -> 15107 -> 1259).
theorem kill2_2_373 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (ha : 1 + 2 ^ 373 ∣ 1 + 2 ^ m) (hd : 1 + 3 ^ 2 ∣ 1 + 3 ^ e) : False := by
  have ha2 : 1 + 2 ^ 373 ∣ 2 ^ m + 1 := by rwa [Nat.add_comm (2 ^ m) 1]
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g60427 : 60427 ∈ P := S2 60427 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 373 = 2 ^ 200 * 2 ^ 173 by rw [← pow_add]]; norm_num : 60427 ∣ 1 + 2 ^ 373).trans ha2)
  have g15107 : 15107 ∈ P := S1 15107 (by norm_num) (by norm_num) (hnz (by norm_num)) 60427 g60427 (by norm_num)
  have g1259 : 1259 ∈ P := S1 1259 (by norm_num) (by norm_num) (hnz (by norm_num)) 15107 g15107 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 2).trans hd) 1259 g1259 (by norm_num)


theorem two_residues_U {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p) :
    m % 62 ≠ 31 ∧
      m % 80 ≠ 40 ∧
      m % 82 ≠ 41 ∧
      m % 86 ≠ 43 ∧
      m % 88 ≠ 44 ∧
      m % 94 ≠ 47 ∧
      m % 98 ≠ 49 ∧
      m % 106 ≠ 53 ∧
      m % 116 ≠ 58 ∧
      m % 122 ≠ 61 ∧
      m % 142 ≠ 71 ∧
      m % 146 ≠ 73 ∧
      m % 158 ≠ 79 ∧
      m % 176 ≠ 88 ∧
      m % 178 ≠ 89 ∧
      m % 184 ≠ 92 ∧
      m % 186 ≠ 93 ∧
      m % 202 ≠ 101 ∧
      m % 206 ≠ 103 ∧
      m % 208 ≠ 104 ∧
      m % 214 ≠ 107 ∧
      m % 218 ≠ 109 ∧
      m % 226 ≠ 113 ∧
      m % 254 ≠ 127 ∧
      m % 256 ≠ 128 ∧
      m % 258 ≠ 129 ∧
      m % 272 ≠ 136 ∧
      m % 274 ≠ 137 ∧
      m % 278 ≠ 139 ∧
      m % 296 ≠ 148 ∧
      m % 302 ≠ 151 ∧
      m % 318 ≠ 159 ∧
      m % 322 ≠ 161 ∧
      m % 326 ≠ 163 ∧
      m % 328 ≠ 164 ∧
      m % 332 ≠ 166 ∧
      m % 334 ≠ 167 ∧
      m % 344 ≠ 172 ∧
      m % 346 ≠ 173 ∧
      m % 348 ≠ 174 ∧
      m % 352 ≠ 176 ∧
      m % 356 ≠ 178 ∧
      m % 358 ≠ 179 ∧
      m % 362 ≠ 181 ∧
      m % 366 ≠ 183 ∧
      m % 368 ≠ 184 ∧
      m % 374 ≠ 187 ∧
      m % 376 ≠ 188 ∧
      m % 382 ≠ 191 ∧
      m % 386 ≠ 193 ∧
      m % 388 ≠ 194 ∧
      m % 394 ≠ 197 ∧
      m % 398 ≠ 199 ∧
      m % 400 ≠ 200 :=
  ⟨fun h => kill2_1_31 hP E (one_add_pow_dvd_of_odd_mul (e0 := 31) (by omega)),
   fun h => kill2_1_40 hP E (one_add_pow_dvd_of_odd_mul (e0 := 40) (by omega)),
   fun h => kill2_1_41 hP E (one_add_pow_dvd_of_odd_mul (e0 := 41) (by omega)),
   fun h => kill2_1_43 hP E (one_add_pow_dvd_of_odd_mul (e0 := 43) (by omega)),
   fun h => kill2_1_44 hP E (one_add_pow_dvd_of_odd_mul (e0 := 44) (by omega)),
   fun h => kill2_1_47 hP E (one_add_pow_dvd_of_odd_mul (e0 := 47) (by omega)),
   fun h => kill2_1_49 hP E (one_add_pow_dvd_of_odd_mul (e0 := 49) (by omega)),
   fun h => kill2_1_53 hP E (one_add_pow_dvd_of_odd_mul (e0 := 53) (by omega)),
   fun h => kill2_1_58 hP E (one_add_pow_dvd_of_odd_mul (e0 := 58) (by omega)),
   fun h => kill2_1_61 hP E (one_add_pow_dvd_of_odd_mul (e0 := 61) (by omega)),
   fun h => kill2_1_71 hP E (one_add_pow_dvd_of_odd_mul (e0 := 71) (by omega)),
   fun h => kill2_1_73 hP E (one_add_pow_dvd_of_odd_mul (e0 := 73) (by omega)),
   fun h => kill2_1_79 hP E (one_add_pow_dvd_of_odd_mul (e0 := 79) (by omega)),
   fun h => kill2_1_88 hP E (one_add_pow_dvd_of_odd_mul (e0 := 88) (by omega)),
   fun h => kill2_1_89 hP E (one_add_pow_dvd_of_odd_mul (e0 := 89) (by omega)),
   fun h => kill2_1_92 hP E (one_add_pow_dvd_of_odd_mul (e0 := 92) (by omega)),
   fun h => kill2_1_93 hP E (one_add_pow_dvd_of_odd_mul (e0 := 93) (by omega)),
   fun h => kill2_1_101 hP E (one_add_pow_dvd_of_odd_mul (e0 := 101) (by omega)),
   fun h => kill2_1_103 hP E (one_add_pow_dvd_of_odd_mul (e0 := 103) (by omega)),
   fun h => kill2_1_104 hP E (one_add_pow_dvd_of_odd_mul (e0 := 104) (by omega)),
   fun h => kill2_1_107 hP E (one_add_pow_dvd_of_odd_mul (e0 := 107) (by omega)),
   fun h => kill2_1_109 hP E (one_add_pow_dvd_of_odd_mul (e0 := 109) (by omega)),
   fun h => kill2_1_113 hP E (one_add_pow_dvd_of_odd_mul (e0 := 113) (by omega)),
   fun h => kill2_1_127 hP E (one_add_pow_dvd_of_odd_mul (e0 := 127) (by omega)),
   fun h => kill2_1_128 hP E (one_add_pow_dvd_of_odd_mul (e0 := 128) (by omega)),
   fun h => kill2_1_129 hP E (one_add_pow_dvd_of_odd_mul (e0 := 129) (by omega)),
   fun h => kill2_1_136 hP E (one_add_pow_dvd_of_odd_mul (e0 := 136) (by omega)),
   fun h => kill2_1_137 hP E (one_add_pow_dvd_of_odd_mul (e0 := 137) (by omega)),
   fun h => kill2_1_139 hP E (one_add_pow_dvd_of_odd_mul (e0 := 139) (by omega)),
   fun h => kill2_1_148 hP E (one_add_pow_dvd_of_odd_mul (e0 := 148) (by omega)),
   fun h => kill2_1_151 hP E (one_add_pow_dvd_of_odd_mul (e0 := 151) (by omega)),
   fun h => kill2_1_159 hP E (one_add_pow_dvd_of_odd_mul (e0 := 159) (by omega)),
   fun h => kill2_1_161 hP E (one_add_pow_dvd_of_odd_mul (e0 := 161) (by omega)),
   fun h => kill2_1_163 hP E (one_add_pow_dvd_of_odd_mul (e0 := 163) (by omega)),
   fun h => kill2_1_164 hP E (one_add_pow_dvd_of_odd_mul (e0 := 164) (by omega)),
   fun h => kill2_1_166 hP E (one_add_pow_dvd_of_odd_mul (e0 := 166) (by omega)),
   fun h => kill2_1_167 hP E (one_add_pow_dvd_of_odd_mul (e0 := 167) (by omega)),
   fun h => kill2_1_172 hP E (one_add_pow_dvd_of_odd_mul (e0 := 172) (by omega)),
   fun h => kill2_1_173 hP E (one_add_pow_dvd_of_odd_mul (e0 := 173) (by omega)),
   fun h => kill2_1_174 hP E (one_add_pow_dvd_of_odd_mul (e0 := 174) (by omega)),
   fun h => kill2_1_176 hP E (one_add_pow_dvd_of_odd_mul (e0 := 176) (by omega)),
   fun h => kill2_1_178 hP E (one_add_pow_dvd_of_odd_mul (e0 := 178) (by omega)),
   fun h => kill2_1_179 hP E (one_add_pow_dvd_of_odd_mul (e0 := 179) (by omega)),
   fun h => kill2_1_181 hP E (one_add_pow_dvd_of_odd_mul (e0 := 181) (by omega)),
   fun h => kill2_1_183 hP E (one_add_pow_dvd_of_odd_mul (e0 := 183) (by omega)),
   fun h => kill2_1_184 hP E (one_add_pow_dvd_of_odd_mul (e0 := 184) (by omega)),
   fun h => kill2_1_187 hP E (one_add_pow_dvd_of_odd_mul (e0 := 187) (by omega)),
   fun h => kill2_1_188 hP E (one_add_pow_dvd_of_odd_mul (e0 := 188) (by omega)),
   fun h => kill2_1_191 hP E (one_add_pow_dvd_of_odd_mul (e0 := 191) (by omega)),
   fun h => kill2_1_193 hP E (one_add_pow_dvd_of_odd_mul (e0 := 193) (by omega)),
   fun h => kill2_1_194 hP E (one_add_pow_dvd_of_odd_mul (e0 := 194) (by omega)),
   fun h => kill2_1_197 hP E (one_add_pow_dvd_of_odd_mul (e0 := 197) (by omega)),
   fun h => kill2_1_199 hP E (one_add_pow_dvd_of_odd_mul (e0 := 199) (by omega)),
   fun h => kill2_1_200 hP E (one_add_pow_dvd_of_odd_mul (e0 := 200) (by omega))⟩

theorem two_residues_X2 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (he : e % 4 = 2) :
    m % 4 ≠ 2 ∧
      m % 12 ≠ 6 ∧
      m % 18 ≠ 9 ∧
      m % 22 ≠ 11 ∧
      m % 26 ≠ 13 ∧
      m % 42 ≠ 21 ∧
      m % 46 ≠ 23 ∧
      m % 316 ≠ 158 ∧
      m % 338 ≠ 169 ∧
      m % 438 ≠ 219 ∧
      m % 544 ≠ 272 ∧
      m % 604 ≠ 302 ∧
      m % 664 ≠ 332 ∧
      m % 712 ≠ 356 ∧
      m % 746 ≠ 373 :=
  ⟨fun h => kill2_2_2 hP E (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_6 hP E (one_add_pow_dvd_of_odd_mul (e0 := 6) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_9 hP E (one_add_pow_dvd_of_odd_mul (e0 := 9) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_11 hP E (one_add_pow_dvd_of_odd_mul (e0 := 11) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_13 hP E (one_add_pow_dvd_of_odd_mul (e0 := 13) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_21 hP E (one_add_pow_dvd_of_odd_mul (e0 := 21) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_23 hP E (one_add_pow_dvd_of_odd_mul (e0 := 23) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_158 hP E (one_add_pow_dvd_of_odd_mul (e0 := 158) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_169 hP E (one_add_pow_dvd_of_odd_mul (e0 := 169) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_219 hP E (one_add_pow_dvd_of_odd_mul (e0 := 219) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_272 hP E (one_add_pow_dvd_of_odd_mul (e0 := 272) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_302 hP E (one_add_pow_dvd_of_odd_mul (e0 := 302) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_332 hP E (one_add_pow_dvd_of_odd_mul (e0 := 332) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_356 hP E (one_add_pow_dvd_of_odd_mul (e0 := 356) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill2_2_373 hP E (one_add_pow_dvd_of_odd_mul (e0 := 373) (by omega))
      (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega))⟩

set_option maxRecDepth 100000 in
theorem set_U {m : ℕ} (h : m % 62 ≠ 31 ∧
      m % 80 ≠ 40 ∧
      m % 82 ≠ 41 ∧
      m % 86 ≠ 43 ∧
      m % 88 ≠ 44 ∧
      m % 94 ≠ 47 ∧
      m % 98 ≠ 49 ∧
      m % 106 ≠ 53 ∧
      m % 116 ≠ 58 ∧
      m % 122 ≠ 61 ∧
      m % 142 ≠ 71 ∧
      m % 146 ≠ 73 ∧
      m % 158 ≠ 79 ∧
      m % 176 ≠ 88 ∧
      m % 178 ≠ 89 ∧
      m % 184 ≠ 92 ∧
      m % 186 ≠ 93 ∧
      m % 202 ≠ 101 ∧
      m % 206 ≠ 103 ∧
      m % 208 ≠ 104 ∧
      m % 214 ≠ 107 ∧
      m % 218 ≠ 109 ∧
      m % 226 ≠ 113 ∧
      m % 254 ≠ 127 ∧
      m % 256 ≠ 128 ∧
      m % 258 ≠ 129 ∧
      m % 272 ≠ 136 ∧
      m % 274 ≠ 137 ∧
      m % 278 ≠ 139 ∧
      m % 296 ≠ 148 ∧
      m % 302 ≠ 151 ∧
      m % 318 ≠ 159 ∧
      m % 322 ≠ 161 ∧
      m % 326 ≠ 163 ∧
      m % 328 ≠ 164 ∧
      m % 332 ≠ 166 ∧
      m % 334 ≠ 167 ∧
      m % 344 ≠ 172 ∧
      m % 346 ≠ 173 ∧
      m % 348 ≠ 174 ∧
      m % 352 ≠ 176 ∧
      m % 356 ≠ 178 ∧
      m % 358 ≠ 179 ∧
      m % 362 ≠ 181 ∧
      m % 366 ≠ 183 ∧
      m % 368 ≠ 184 ∧
      m % 374 ≠ 187 ∧
      m % 376 ≠ 188 ∧
      m % 382 ≠ 191 ∧
      m % 386 ≠ 193 ∧
      m % 388 ≠ 194 ∧
      m % 394 ≠ 197 ∧
      m % 398 ≠ 199 ∧
      m % 400 ≠ 200) :
    ∀ d ∈ ({31, 40, 41, 43, 44, 47, 49, 53, 58, 61, 71, 73, 79, 88, 89, 92, 93, 101, 103, 104, 107, 109,
        113, 127, 128, 129, 136, 137, 139, 148, 151, 159, 161, 163, 164, 166, 167, 172, 173,
        174, 176, 178, 179, 181, 183, 184, 187, 188, 191, 193, 194, 197, 199, 200} : Finset ℕ), m % (2 * d) ≠ d := by
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15, u16, u17, u18, u19, u20, u21, u22, u23, u24, u25, u26, u27, u28, u29, u30, u31, u32, u33, u34, u35, u36, u37, u38, u39, u40, u41, u42, u43, u44, u45, u46, u47, u48, u49, u50, u51, u52, u53⟩ := h
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

set_option maxRecDepth 100000 in
theorem set_X2 {m : ℕ} (h : m % 4 ≠ 2 ∧
      m % 12 ≠ 6 ∧
      m % 18 ≠ 9 ∧
      m % 22 ≠ 11 ∧
      m % 26 ≠ 13 ∧
      m % 42 ≠ 21 ∧
      m % 46 ≠ 23 ∧
      m % 316 ≠ 158 ∧
      m % 338 ≠ 169 ∧
      m % 438 ≠ 219 ∧
      m % 544 ≠ 272 ∧
      m % 604 ≠ 302 ∧
      m % 664 ≠ 332 ∧
      m % 712 ≠ 356 ∧
      m % 746 ≠ 373) :
    ∀ d ∈ ({2, 6, 9, 11, 13, 21, 23, 158, 169, 219, 272, 302, 332, 356, 373} : Finset ℕ), m % (2 * d) ≠ d := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14⟩ := h
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max A1 A2, fun n h hiff hbig hS hG => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  have h3sq := (hiff 3).mpr rfl
  have he2 : 2 ≤ n.factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hn0).mp h3sq.2.2
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  have rU := set_U (two_residues_U hP E)
  rw [ha] at rU
  by_cases he : n.factorization 3 % 4 = 2
  · have rX := set_X2 (two_residues_X2 hP E he)
    rw [ha] at rX
    exact (h1 n h hiff hbig he hS hG rU rX).trans (le_max_left _ _)
  · exact (h2 n h hiff hbig he hS hG rU).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1
