import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H2.R1.H1.R1
-- Credit: @adammcarter
-- Splits step H1 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H2.R1 (5 is the only repeated odd prime,
-- 5^4 exactly divides n, a = padicValNat 2 n = 2 mod 4, a >= 128, no prime 7..420 divides a, and
-- 15, 25, 27 do not divide a) after extending the prime sieve past 420.  Proving H1 and H2 proves
-- the step.
--
-- Notation as in the parent: balance equation (2^a + 1)(1 + 5^4) prod_P (p + 1) = 2^(a+1) 5^4
-- prod_P p; 1 + 5^4 = 2 * 313 forces the simple primes 313, 157, 79 (and one factor 5 in 80).
-- For a = 2 mod 4 and q odd, q | a makes a an odd multiple of 2q, so 2^(2q) + 1 | 2^a + 1.
--
-- PROVED BELOW (nsieve, lemmas kq_d<2q>): no prime q in the list of the hypotheses divides a:
-- the 78 primes from 421 to 1013 other than 601, 653, 683, 751, 811, 821, 967, 977, 983, 991, 1009.  Each chain starts at prime
-- factors of 2^(2q) + 1 (factordb, queried with the bare expression, re-checked by divisibility in
-- Lean; PARI and GMP-ECM for the p + 1 and p - 1) and ends at a prime with two sources, a square,
-- or more than four factors of 5.  157 Lucas certificates up to 92 digits.  The excluded primes have
-- no chain found (653, 751, 811, 821) or a certificate over the size budget of this file.
-- So a = 2 t r with t in {1, 3, 5, 9} and r a product of primes above 420 that are excepted above
-- or above 1013.
--
-- H1 (OPEN): as the parent, with the new sieve, and 3 or 5 divides a.
-- H2 (OPEN): as the parent, with the new sieve, and neither 3 nor 5 divides a.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts S_sq zmod_ne_one)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (hK5 setup mod_of_dvd_two_mod_four)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1 (tpd)

-- H1: the parent family with the new sieve, 3 or 5 dividing a.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 4 →
    padicValNat 2 n % 4 = 2 → 128 ≤ padicValNat 2 n →
    (∀ q, q.Prime → 7 ≤ q → q ≤ 420 → ¬ q ∣ padicValNat 2 n) →
    ¬ 15 ∣ padicValNat 2 n → ¬ 25 ∣ padicValNat 2 n → ¬ 27 ∣ padicValNat 2 n →
    (∀ q ∈ ({421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 607, 613, 617, 619, 631, 641, 643, 647, 659, 661, 673, 677, 691, 701, 709, 719, 727, 733, 739, 743, 757, 761, 769, 773, 787, 797, 809, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 971, 997, 1013} : Finset ℕ), ¬ q ∣ padicValNat 2 n) →
    (3 ∣ padicValNat 2 n ∨ 5 ∣ padicValNat 2 n) →
    padicValNat 2 n ≤ A

-- H2: the parent family with the new sieve, neither 3 nor 5 dividing a.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 4 →
    padicValNat 2 n % 4 = 2 → 128 ≤ padicValNat 2 n →
    (∀ q, q.Prime → 7 ≤ q → q ≤ 420 → ¬ q ∣ padicValNat 2 n) →
    ¬ 15 ∣ padicValNat 2 n → ¬ 25 ∣ padicValNat 2 n → ¬ 27 ∣ padicValNat 2 n →
    (∀ q ∈ ({421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 607, 613, 617, 619, 631, 641, 643, 647, 659, 661, 673, 677, 691, 701, 709, 719, 727, 733, 739, 743, 757, 761, 769, 773, 787, 797, 809, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 971, 997, 1013} : Finset ℕ), ¬ q ∣ padicValNat 2 n) →
    ¬ 3 ∣ padicValNat 2 n → ¬ 5 ∣ padicValNat 2 n →
    padicValNat 2 n ≤ A

-- Section 1. Lucas certificates and chain lemmas.

theorem prime_3596696359 : Nat.Prime 3596696359 := by
  refine lucas_primality 3596696359 (3 : ZMod 3596696359) ?_ (fun q hq hd => ?_)
  · rw [show 3596696359 - 1 = 3596696358 from by norm_num]
    reduce_mod_char
  · have e : 3596696359 - 1 = [2 ^ 1, 3 ^ 1, 17 ^ 1, 79 ^ 1, 157 ^ 1, 2843 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3596696359 - 1) / 2 = 1798348179 from by norm_num]
      have h2 : (3 : ZMod 3596696359) ^ 1798348179 = ((3596696358 : ℕ) : ZMod 3596696359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3596696359 - 1) / 3 = 1198898786 from by norm_num]
      have h2 : (3 : ZMod 3596696359) ^ 1198898786 = ((1056440925 : ℕ) : ZMod 3596696359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3596696359 - 1) / 17 = 211570374 from by norm_num]
      have h2 : (3 : ZMod 3596696359) ^ 211570374 = ((1551653983 : ℕ) : ZMod 3596696359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3596696359 - 1) / 79 = 45527802 from by norm_num]
      have h2 : (3 : ZMod 3596696359) ^ 45527802 = ((3296927592 : ℕ) : ZMod 3596696359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3596696359 - 1) / 157 = 22908894 from by norm_num]
      have h2 : (3 : ZMod 3596696359) ^ 22908894 = ((1418280523 : ℕ) : ZMod 3596696359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3596696359 - 1) / 2843 = 1265106 from by norm_num]
      have h2 : (3 : ZMod 3596696359) ^ 1265106 = ((1564753049 : ℕ) : ZMod 3596696359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_44210591644829 : Nat.Prime 44210591644829 := by
  refine lucas_primality 44210591644829 (3 : ZMod 44210591644829) ?_ (fun q hq hd => ?_)
  · rw [show 44210591644829 - 1 = 44210591644828 from by norm_num]
    reduce_mod_char
  · have e : 44210591644829 - 1 = [2 ^ 2, 7 ^ 1, 439 ^ 1, 3596696359 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44210591644829 - 1) / 2 = 22105295822414 from by norm_num]
      have h2 : (3 : ZMod 44210591644829) ^ 22105295822414 = ((44210591644828 : ℕ) : ZMod 44210591644829) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44210591644829 - 1) / 7 = 6315798806404 from by norm_num]
      have h2 : (3 : ZMod 44210591644829) ^ 6315798806404 = ((44106508308176 : ℕ) : ZMod 44210591644829) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44210591644829 - 1) / 439 = 100707498052 from by norm_num]
      have h2 : (3 : ZMod 44210591644829) ^ 100707498052 = ((39812545133725 : ℕ) : ZMod 44210591644829) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3596696359).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44210591644829 - 1) / 3596696359 = 12292 from by norm_num]
      have h2 : (3 : ZMod 44210591644829) ^ 12292 = ((42066094951604 : ℕ) : ZMod 44210591644829) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_155235953 : Nat.Prime 155235953 := by
  refine lucas_primality 155235953 (3 : ZMod 155235953) ?_ (fun q hq hd => ?_)
  · rw [show 155235953 - 1 = 155235952 from by norm_num]
    reduce_mod_char
  · have e : 155235953 - 1 = [2 ^ 4, 9702247 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155235953 - 1) / 2 = 77617976 from by norm_num]
      have h2 : (3 : ZMod 155235953) ^ 77617976 = ((155235952 : ℕ) : ZMod 155235953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155235953 - 1) / 9702247 = 16 from by norm_num]
      have h2 : (3 : ZMod 155235953) ^ 16 = ((43046721 : ℕ) : ZMod 155235953) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_893491554811898017 : Nat.Prime 893491554811898017 := by
  refine lucas_primality 893491554811898017 (5 : ZMod 893491554811898017) ?_ (fun q hq hd => ?_)
  · rw [show 893491554811898017 - 1 = 893491554811898016 from by norm_num]
    reduce_mod_char
  · have e : 893491554811898017 - 1 = [2 ^ 5, 3 ^ 2, 13 ^ 1, 37 ^ 1, 41549 ^ 1, 155235953 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (893491554811898017 - 1) / 2 = 446745777405949008 from by norm_num]
      have h2 : (5 : ZMod 893491554811898017) ^ 446745777405949008 = ((893491554811898016 : ℕ) : ZMod 893491554811898017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (893491554811898017 - 1) / 3 = 297830518270632672 from by norm_num]
      have h2 : (5 : ZMod 893491554811898017) ^ 297830518270632672 = ((452981030315784017 : ℕ) : ZMod 893491554811898017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (893491554811898017 - 1) / 13 = 68730119600915232 from by norm_num]
      have h2 : (5 : ZMod 893491554811898017) ^ 68730119600915232 = ((183488846159692018 : ℕ) : ZMod 893491554811898017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (893491554811898017 - 1) / 37 = 24148420400321568 from by norm_num]
      have h2 : (5 : ZMod 893491554811898017) ^ 24148420400321568 = ((384824259826765279 : ℕ) : ZMod 893491554811898017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (893491554811898017 - 1) / 41549 = 21504526097184 from by norm_num]
      have h2 : (5 : ZMod 893491554811898017) ^ 21504526097184 = ((727848764667504673 : ℕ) : ZMod 893491554811898017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_155235953).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (893491554811898017 - 1) / 155235953 = 5755699872 from by norm_num]
      have h2 : (5 : ZMod 893491554811898017) ^ 5755699872 = ((42728786574522355 : ℕ) : ZMod 893491554811898017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1568971170249692917853 : Nat.Prime 1568971170249692917853 := by
  refine lucas_primality 1568971170249692917853 (3 : ZMod 1568971170249692917853) ?_ (fun q hq hd => ?_)
  · rw [show 1568971170249692917853 - 1 = 1568971170249692917852 from by norm_num]
    reduce_mod_char
  · have e : 1568971170249692917853 - 1 = [2 ^ 2, 439 ^ 1, 893491554811898017 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1568971170249692917853 - 1) / 2 = 784485585124846458926 from by norm_num]
      have h2 : (3 : ZMod 1568971170249692917853) ^ 784485585124846458926 = ((1568971170249692917852 : ℕ) : ZMod 1568971170249692917853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1568971170249692917853 - 1) / 439 = 3573966219247592068 from by norm_num]
      have h2 : (3 : ZMod 1568971170249692917853) ^ 3573966219247592068 = ((279274376822873951259 : ℕ) : ZMod 1568971170249692917853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_893491554811898017).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1568971170249692917853 - 1) / 893491554811898017 = 1756 from by norm_num]
      have h2 : (3 : ZMod 1568971170249692917853) ^ 1756 = ((213908933854349264650 : ℕ) : ZMod 1568971170249692917853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_773339215189 : Nat.Prime 773339215189 := by
  refine lucas_primality 773339215189 (6 : ZMod 773339215189) ?_ (fun q hq hd => ?_)
  · rw [show 773339215189 - 1 = 773339215188 from by norm_num]
    reduce_mod_char
  · have e : 773339215189 - 1 = [2 ^ 2, 3 ^ 1, 443 ^ 1, 9283 ^ 1, 15671 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (773339215189 - 1) / 2 = 386669607594 from by norm_num]
      have h2 : (6 : ZMod 773339215189) ^ 386669607594 = ((773339215188 : ℕ) : ZMod 773339215189) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (773339215189 - 1) / 3 = 257779738396 from by norm_num]
      have h2 : (6 : ZMod 773339215189) ^ 257779738396 = ((155290553265 : ℕ) : ZMod 773339215189) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (773339215189 - 1) / 443 = 1745686716 from by norm_num]
      have h2 : (6 : ZMod 773339215189) ^ 1745686716 = ((562775564524 : ℕ) : ZMod 773339215189) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (773339215189 - 1) / 9283 = 83307036 from by norm_num]
      have h2 : (6 : ZMod 773339215189) ^ 83307036 = ((666589429477 : ℕ) : ZMod 773339215189) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (773339215189 - 1) / 15671 = 49348428 from by norm_num]
      have h2 : (6 : ZMod 773339215189) ^ 49348428 = ((614176252995 : ℕ) : ZMod 773339215189) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_160850603 : Nat.Prime 160850603 := by
  refine lucas_primality 160850603 (2 : ZMod 160850603) ?_ (fun q hq hd => ?_)
  · rw [show 160850603 - 1 = 160850602 from by norm_num]
    reduce_mod_char
  · have e : 160850603 - 1 = [2 ^ 1, 11 ^ 1, 2689 ^ 1, 2719 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (160850603 - 1) / 2 = 80425301 from by norm_num]
      have h2 : (2 : ZMod 160850603) ^ 80425301 = ((160850602 : ℕ) : ZMod 160850603) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (160850603 - 1) / 11 = 14622782 from by norm_num]
      have h2 : (2 : ZMod 160850603) ^ 14622782 = ((83454232 : ℕ) : ZMod 160850603) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (160850603 - 1) / 2689 = 59818 from by norm_num]
      have h2 : (2 : ZMod 160850603) ^ 59818 = ((31756933 : ℕ) : ZMod 160850603) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (160850603 - 1) / 2719 = 59158 from by norm_num]
      have h2 : (2 : ZMod 160850603) ^ 59158 = ((20448266 : ℕ) : ZMod 160850603) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_426491518463 : Nat.Prime 426491518463 := by
  refine lucas_primality 426491518463 (5 : ZMod 426491518463) ?_ (fun q hq hd => ?_)
  · rw [show 426491518463 - 1 = 426491518462 from by norm_num]
    reduce_mod_char
  · have e : 426491518463 - 1 = [2 ^ 1, 103 ^ 1, 9631 ^ 1, 214967 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (426491518463 - 1) / 2 = 213245759231 from by norm_num]
      have h2 : (5 : ZMod 426491518463) ^ 213245759231 = ((426491518462 : ℕ) : ZMod 426491518463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (426491518463 - 1) / 103 = 4140694354 from by norm_num]
      have h2 : (5 : ZMod 426491518463) ^ 4140694354 = ((261757836613 : ℕ) : ZMod 426491518463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (426491518463 - 1) / 9631 = 44283202 from by norm_num]
      have h2 : (5 : ZMod 426491518463) ^ 44283202 = ((154805474759 : ℕ) : ZMod 426491518463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (426491518463 - 1) / 214967 = 1983986 from by norm_num]
      have h2 : (5 : ZMod 426491518463) ^ 1983986 = ((425712689227 : ℕ) : ZMod 426491518463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_242119958550901823461310734391 : Nat.Prime 242119958550901823461310734391 := by
  refine lucas_primality 242119958550901823461310734391 (13 : ZMod 242119958550901823461310734391) ?_ (fun q hq hd => ?_)
  · rw [show 242119958550901823461310734391 - 1 = 242119958550901823461310734390 from by norm_num]
    reduce_mod_char
  · have e : 242119958550901823461310734391 - 1 = [2 ^ 1, 5 ^ 1, 3329 ^ 1, 106019 ^ 1, 160850603 ^ 1, 426491518463 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242119958550901823461310734391 - 1) / 2 = 121059979275450911730655367195 from by norm_num]
      have h2 : (13 : ZMod 242119958550901823461310734391) ^ 121059979275450911730655367195 = ((242119958550901823461310734390 : ℕ) : ZMod 242119958550901823461310734391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242119958550901823461310734391 - 1) / 5 = 48423991710180364692262146878 from by norm_num]
      have h2 : (13 : ZMod 242119958550901823461310734391) ^ 48423991710180364692262146878 = ((184179303847964130889269880427 : ℕ) : ZMod 242119958550901823461310734391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242119958550901823461310734391 - 1) / 3329 = 72730537263713374425145910 from by norm_num]
      have h2 : (13 : ZMod 242119958550901823461310734391) ^ 72730537263713374425145910 = ((11249539183765347257942386664 : ℕ) : ZMod 242119958550901823461310734391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242119958550901823461310734391 - 1) / 106019 = 2283741202528809208361810 from by norm_num]
      have h2 : (13 : ZMod 242119958550901823461310734391) ^ 2283741202528809208361810 = ((7301829432234550709754107138 : ℕ) : ZMod 242119958550901823461310734391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_160850603).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242119958550901823461310734391 - 1) / 160850603 = 1505247441011469652130 from by norm_num]
      have h2 : (13 : ZMod 242119958550901823461310734391) ^ 1505247441011469652130 = ((73245664945501445045538991023 : ℕ) : ZMod 242119958550901823461310734391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_426491518463).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242119958550901823461310734391 - 1) / 426491518463 = 567701696445123530 from by norm_num]
      have h2 : (13 : ZMod 242119958550901823461310734391) ^ 567701696445123530 = ((18850144674417855242205237479 : ℕ) : ZMod 242119958550901823461310734391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6196333979234679466021864314534473 : Nat.Prime 6196333979234679466021864314534473 := by
  refine lucas_primality 6196333979234679466021864314534473 (3 : ZMod 6196333979234679466021864314534473) ?_ (fun q hq hd => ?_)
  · rw [show 6196333979234679466021864314534473 - 1 = 6196333979234679466021864314534472 from by norm_num]
    reduce_mod_char
  · have e : 6196333979234679466021864314534473 - 1 = [2 ^ 3, 7 ^ 1, 457 ^ 1, 242119958550901823461310734391 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6196333979234679466021864314534473 - 1) / 2 = 3098166989617339733010932157267236 from by norm_num]
      have h2 : (3 : ZMod 6196333979234679466021864314534473) ^ 3098166989617339733010932157267236 = ((6196333979234679466021864314534472 : ℕ) : ZMod 6196333979234679466021864314534473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6196333979234679466021864314534473 - 1) / 7 = 885190568462097066574552044933496 from by norm_num]
      have h2 : (3 : ZMod 6196333979234679466021864314534473) ^ 885190568462097066574552044933496 = ((35944975758975907735893304592563 : ℕ) : ZMod 6196333979234679466021864314534473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6196333979234679466021864314534473 - 1) / 457 = 13558717678850502113833401125896 from by norm_num]
      have h2 : (3 : ZMod 6196333979234679466021864314534473) ^ 13558717678850502113833401125896 = ((3047268564992815702037391016764895 : ℕ) : ZMod 6196333979234679466021864314534473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_242119958550901823461310734391).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6196333979234679466021864314534473 - 1) / 242119958550901823461310734391 = 25592 from by norm_num]
      have h2 : (3 : ZMod 6196333979234679466021864314534473) ^ 25592 = ((2465339489637023547409768066502567 : ℕ) : ZMod 6196333979234679466021864314534473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1016703097 : Nat.Prime 1016703097 := by
  refine lucas_primality 1016703097 (13 : ZMod 1016703097) ?_ (fun q hq hd => ?_)
  · rw [show 1016703097 - 1 = 1016703096 from by norm_num]
    reduce_mod_char
  · have e : 1016703097 - 1 = [2 ^ 3, 3 ^ 1, 42362629 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1016703097 - 1) / 2 = 508351548 from by norm_num]
      have h2 : (13 : ZMod 1016703097) ^ 508351548 = ((1016703096 : ℕ) : ZMod 1016703097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1016703097 - 1) / 3 = 338901032 from by norm_num]
      have h2 : (13 : ZMod 1016703097) ^ 338901032 = ((690531 : ℕ) : ZMod 1016703097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1016703097 - 1) / 42362629 = 24 from by norm_num]
      have h2 : (13 : ZMod 1016703097) ^ 24 = ((786538308 : ℕ) : ZMod 1016703097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_57461741 : Nat.Prime 57461741 := by
  refine lucas_primality 57461741 (11 : ZMod 57461741) ?_ (fun q hq hd => ?_)
  · rw [show 57461741 - 1 = 57461740 from by norm_num]
    reduce_mod_char
  · have e : 57461741 - 1 = [2 ^ 2, 5 ^ 1, 7 ^ 1, 37 ^ 1, 11093 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57461741 - 1) / 2 = 28730870 from by norm_num]
      have h2 : (11 : ZMod 57461741) ^ 28730870 = ((57461740 : ℕ) : ZMod 57461741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57461741 - 1) / 5 = 11492348 from by norm_num]
      have h2 : (11 : ZMod 57461741) ^ 11492348 = ((34048771 : ℕ) : ZMod 57461741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57461741 - 1) / 7 = 8208820 from by norm_num]
      have h2 : (11 : ZMod 57461741) ^ 8208820 = ((41090740 : ℕ) : ZMod 57461741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57461741 - 1) / 37 = 1553020 from by norm_num]
      have h2 : (11 : ZMod 57461741) ^ 1553020 = ((7019133 : ℕ) : ZMod 57461741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57461741 - 1) / 11093 = 5180 from by norm_num]
      have h2 : (11 : ZMod 57461741) ^ 5180 = ((28547937 : ℕ) : ZMod 57461741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_114923483 : Nat.Prime 114923483 := by
  refine lucas_primality 114923483 (2 : ZMod 114923483) ?_ (fun q hq hd => ?_)
  · rw [show 114923483 - 1 = 114923482 from by norm_num]
    reduce_mod_char
  · have e : 114923483 - 1 = [2 ^ 1, 57461741 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (114923483 - 1) / 2 = 57461741 from by norm_num]
      have h2 : (2 : ZMod 114923483) ^ 57461741 = ((114923482 : ℕ) : ZMod 114923483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_57461741).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (114923483 - 1) / 57461741 = 2 from by norm_num]
      have h2 : (2 : ZMod 114923483) ^ 2 = ((4 : ℕ) : ZMod 114923483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3263089108439141 : Nat.Prime 3263089108439141 := by
  refine lucas_primality 3263089108439141 (2 : ZMod 3263089108439141) ?_ (fun q hq hd => ?_)
  · rw [show 3263089108439141 - 1 = 3263089108439140 from by norm_num]
    reduce_mod_char
  · have e : 3263089108439141 - 1 = [2 ^ 2, 5 ^ 1, 1419679 ^ 1, 114923483 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3263089108439141 - 1) / 2 = 1631544554219570 from by norm_num]
      have h2 : (2 : ZMod 3263089108439141) ^ 1631544554219570 = ((3263089108439140 : ℕ) : ZMod 3263089108439141) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3263089108439141 - 1) / 5 = 652617821687828 from by norm_num]
      have h2 : (2 : ZMod 3263089108439141) ^ 652617821687828 = ((284315626031674 : ℕ) : ZMod 3263089108439141) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3263089108439141 - 1) / 1419679 = 2298469660 from by norm_num]
      have h2 : (2 : ZMod 3263089108439141) ^ 2298469660 = ((2000549954816539 : ℕ) : ZMod 3263089108439141) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_114923483).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3263089108439141 - 1) / 114923483 = 28393580 from by norm_num]
      have h2 : (2 : ZMod 3263089108439141) ^ 28393580 = ((1286757473165251 : ℕ) : ZMod 3263089108439141) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1348559743 : Nat.Prime 1348559743 := by
  refine lucas_primality 1348559743 (5 : ZMod 1348559743) ?_ (fun q hq hd => ?_)
  · rw [show 1348559743 - 1 = 1348559742 from by norm_num]
    reduce_mod_char
  · have e : 1348559743 - 1 = [2 ^ 1, 3 ^ 1, 2441 ^ 1, 92077 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1348559743 - 1) / 2 = 674279871 from by norm_num]
      have h2 : (5 : ZMod 1348559743) ^ 674279871 = ((1348559742 : ℕ) : ZMod 1348559743) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1348559743 - 1) / 3 = 449519914 from by norm_num]
      have h2 : (5 : ZMod 1348559743) ^ 449519914 = ((510991437 : ℕ) : ZMod 1348559743) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1348559743 - 1) / 2441 = 552462 from by norm_num]
      have h2 : (5 : ZMod 1348559743) ^ 552462 = ((734222768 : ℕ) : ZMod 1348559743) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1348559743 - 1) / 92077 = 14646 from by norm_num]
      have h2 : (5 : ZMod 1348559743) ^ 14646 = ((1073840945 : ℕ) : ZMod 1348559743) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_169571626806830167 : Nat.Prime 169571626806830167 := by
  refine lucas_primality 169571626806830167 (3 : ZMod 169571626806830167) ?_ (fun q hq hd => ?_)
  · rw [show 169571626806830167 - 1 = 169571626806830166 from by norm_num]
    reduce_mod_char
  · have e : 169571626806830167 - 1 = [2 ^ 1, 3 ^ 2, 107 ^ 1, 65287 ^ 1, 1348559743 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169571626806830167 - 1) / 2 = 84785813403415083 from by norm_num]
      have h2 : (3 : ZMod 169571626806830167) ^ 84785813403415083 = ((169571626806830166 : ℕ) : ZMod 169571626806830167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169571626806830167 - 1) / 3 = 56523875602276722 from by norm_num]
      have h2 : (3 : ZMod 169571626806830167) ^ 56523875602276722 = ((151892933797687313 : ℕ) : ZMod 169571626806830167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169571626806830167 - 1) / 107 = 1584781558942338 from by norm_num]
      have h2 : (3 : ZMod 169571626806830167) ^ 1584781558942338 = ((87257262424252712 : ℕ) : ZMod 169571626806830167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169571626806830167 - 1) / 65287 = 2597326065018 from by norm_num]
      have h2 : (3 : ZMod 169571626806830167) ^ 2597326065018 = ((75797482473575233 : ℕ) : ZMod 169571626806830167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1348559743).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169571626806830167 - 1) / 1348559743 = 125742762 from by norm_num]
      have h2 : (3 : ZMod 169571626806830167) ^ 125742762 = ((157928168693678368 : ℕ) : ZMod 169571626806830167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5845296257595668545524969937697507923682374822769 : Nat.Prime 5845296257595668545524969937697507923682374822769 := by
  refine lucas_primality 5845296257595668545524969937697507923682374822769 (3 : ZMod 5845296257595668545524969937697507923682374822769) ?_ (fun q hq hd => ?_)
  · rw [show 5845296257595668545524969937697507923682374822769 - 1 = 5845296257595668545524969937697507923682374822768 from by norm_num]
    reduce_mod_char
  · have e : 5845296257595668545524969937697507923682374822769 - 1 = [2 ^ 4, 7 ^ 2, 29 ^ 1, 457 ^ 1, 1016703097 ^ 1, 3263089108439141 ^ 1, 169571626806830167 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5845296257595668545524969937697507923682374822769 - 1) / 2 = 2922648128797834272762484968848753961841187411384 from by norm_num]
      have h2 : (3 : ZMod 5845296257595668545524969937697507923682374822769) ^ 2922648128797834272762484968848753961841187411384 = ((5845296257595668545524969937697507923682374822768 : ℕ) : ZMod 5845296257595668545524969937697507923682374822769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5845296257595668545524969937697507923682374822769 - 1) / 7 = 835042322513666935074995705385358274811767831824 from by norm_num]
      have h2 : (3 : ZMod 5845296257595668545524969937697507923682374822769) ^ 835042322513666935074995705385358274811767831824 = ((184672618265170482677724241896478699919608229939 : ℕ) : ZMod 5845296257595668545524969937697507923682374822769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5845296257595668545524969937697507923682374822769 - 1) / 29 = 201561939917092018811205859920603721506288786992 from by norm_num]
      have h2 : (3 : ZMod 5845296257595668545524969937697507923682374822769) ^ 201561939917092018811205859920603721506288786992 = ((1104876850150292595642116612889467869103647181054 : ℕ) : ZMod 5845296257595668545524969937697507923682374822769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5845296257595668545524969937697507923682374822769 - 1) / 457 = 12790582620559449771389430935880761320967997424 from by norm_num]
      have h2 : (3 : ZMod 5845296257595668545524969937697507923682374822769) ^ 12790582620559449771389430935880761320967997424 = ((234743071796191187804603280542665218981250971451 : ℕ) : ZMod 5845296257595668545524969937697507923682374822769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1016703097).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5845296257595668545524969937697507923682374822769 - 1) / 1016703097 = 5749265714684518705193803435121736354544 from by norm_num]
      have h2 : (3 : ZMod 5845296257595668545524969937697507923682374822769) ^ 5749265714684518705193803435121736354544 = ((2546588599629989583467821227145403461617758242108 : ℕ) : ZMod 5845296257595668545524969937697507923682374822769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3263089108439141).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5845296257595668545524969937697507923682374822769 - 1) / 3263089108439141 = 1791338226859423688543566355984048 from by norm_num]
      have h2 : (3 : ZMod 5845296257595668545524969937697507923682374822769) ^ 1791338226859423688543566355984048 = ((1612906029748559539987609221635357075131344262829 : ℕ) : ZMod 5845296257595668545524969937697507923682374822769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_169571626806830167).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5845296257595668545524969937697507923682374822769 - 1) / 169571626806830167 = 34470957008948304507886177356304 from by norm_num]
      have h2 : (3 : ZMod 5845296257595668545524969937697507923682374822769) ^ 34470957008948304507886177356304 = ((4001179960629011823990873860353351194520303058441 : ℕ) : ZMod 5845296257595668545524969937697507923682374822769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_16694937341 : Nat.Prime 16694937341 := by
  refine lucas_primality 16694937341 (3 : ZMod 16694937341) ?_ (fun q hq hd => ?_)
  · rw [show 16694937341 - 1 = 16694937340 from by norm_num]
    reduce_mod_char
  · have e : 16694937341 - 1 = [2 ^ 2, 5 ^ 1, 463 ^ 1, 1802909 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16694937341 - 1) / 2 = 8347468670 from by norm_num]
      have h2 : (3 : ZMod 16694937341) ^ 8347468670 = ((16694937340 : ℕ) : ZMod 16694937341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16694937341 - 1) / 5 = 3338987468 from by norm_num]
      have h2 : (3 : ZMod 16694937341) ^ 3338987468 = ((5809775560 : ℕ) : ZMod 16694937341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16694937341 - 1) / 463 = 36058180 from by norm_num]
      have h2 : (3 : ZMod 16694937341) ^ 36058180 = ((3746056987 : ℕ) : ZMod 16694937341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16694937341 - 1) / 1802909 = 9260 from by norm_num]
      have h2 : (3 : ZMod 16694937341) ^ 9260 = ((3054987623 : ℕ) : ZMod 16694937341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_501334663 : Nat.Prime 501334663 := by
  refine lucas_primality 501334663 (5 : ZMod 501334663) ?_ (fun q hq hd => ?_)
  · rw [show 501334663 - 1 = 501334662 from by norm_num]
    reduce_mod_char
  · have e : 501334663 - 1 = [2 ^ 1, 3 ^ 1, 197 ^ 2, 2153 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (501334663 - 1) / 2 = 250667331 from by norm_num]
      have h2 : (5 : ZMod 501334663) ^ 250667331 = ((501334662 : ℕ) : ZMod 501334663) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (501334663 - 1) / 3 = 167111554 from by norm_num]
      have h2 : (5 : ZMod 501334663) ^ 167111554 = ((213282261 : ℕ) : ZMod 501334663) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (501334663 - 1) / 197 = 2544846 from by norm_num]
      have h2 : (5 : ZMod 501334663) ^ 2544846 = ((57681829 : ℕ) : ZMod 501334663) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (501334663 - 1) / 2153 = 232854 from by norm_num]
      have h2 : (5 : ZMod 501334663) ^ 232854 = ((212968175 : ℕ) : ZMod 501334663) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_130372757 : Nat.Prime 130372757 := by
  refine lucas_primality 130372757 (2 : ZMod 130372757) ?_ (fun q hq hd => ?_)
  · rw [show 130372757 - 1 = 130372756 from by norm_num]
    reduce_mod_char
  · have e : 130372757 - 1 = [2 ^ 2, 19 ^ 1, 37 ^ 1, 71 ^ 1, 653 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (130372757 - 1) / 2 = 65186378 from by norm_num]
      have h2 : (2 : ZMod 130372757) ^ 65186378 = ((130372756 : ℕ) : ZMod 130372757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (130372757 - 1) / 19 = 6861724 from by norm_num]
      have h2 : (2 : ZMod 130372757) ^ 6861724 = ((67481052 : ℕ) : ZMod 130372757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (130372757 - 1) / 37 = 3523588 from by norm_num]
      have h2 : (2 : ZMod 130372757) ^ 3523588 = ((7439888 : ℕ) : ZMod 130372757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (130372757 - 1) / 71 = 1836236 from by norm_num]
      have h2 : (2 : ZMod 130372757) ^ 1836236 = ((31194713 : ℕ) : ZMod 130372757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (130372757 - 1) / 653 = 199652 from by norm_num]
      have h2 : (2 : ZMod 130372757) ^ 199652 = ((87906977 : ℕ) : ZMod 130372757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_154484861 : Nat.Prime 154484861 := by
  refine lucas_primality 154484861 (2 : ZMod 154484861) ?_ (fun q hq hd => ?_)
  · rw [show 154484861 - 1 = 154484860 from by norm_num]
    reduce_mod_char
  · have e : 154484861 - 1 = [2 ^ 2, 5 ^ 1, 157 ^ 1, 49199 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (154484861 - 1) / 2 = 77242430 from by norm_num]
      have h2 : (2 : ZMod 154484861) ^ 77242430 = ((154484860 : ℕ) : ZMod 154484861) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (154484861 - 1) / 5 = 30896972 from by norm_num]
      have h2 : (2 : ZMod 154484861) ^ 30896972 = ((115017886 : ℕ) : ZMod 154484861) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (154484861 - 1) / 157 = 983980 from by norm_num]
      have h2 : (2 : ZMod 154484861) ^ 983980 = ((141933759 : ℕ) : ZMod 154484861) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (154484861 - 1) / 49199 = 3140 from by norm_num]
      have h2 : (2 : ZMod 154484861) ^ 3140 = ((54461173 : ℕ) : ZMod 154484861) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_308969723 : Nat.Prime 308969723 := by
  refine lucas_primality 308969723 (2 : ZMod 308969723) ?_ (fun q hq hd => ?_)
  · rw [show 308969723 - 1 = 308969722 from by norm_num]
    reduce_mod_char
  · have e : 308969723 - 1 = [2 ^ 1, 154484861 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308969723 - 1) / 2 = 154484861 from by norm_num]
      have h2 : (2 : ZMod 308969723) ^ 154484861 = ((308969722 : ℕ) : ZMod 308969723) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_154484861).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308969723 - 1) / 154484861 = 2 from by norm_num]
      have h2 : (2 : ZMod 308969723) ^ 2 = ((4 : ℕ) : ZMod 308969723) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6308060192645687075593549 : Nat.Prime 6308060192645687075593549 := by
  refine lucas_primality 6308060192645687075593549 (7 : ZMod 6308060192645687075593549) ?_ (fun q hq hd => ?_)
  · rw [show 6308060192645687075593549 - 1 = 6308060192645687075593548 from by norm_num]
    reduce_mod_char
  · have e : 6308060192645687075593549 - 1 = [2 ^ 2, 3 ^ 2, 23 ^ 1, 31 ^ 1, 6101 ^ 1, 130372757 ^ 1, 308969723 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6308060192645687075593549 - 1) / 2 = 3154030096322843537796774 from by norm_num]
      have h2 : (7 : ZMod 6308060192645687075593549) ^ 3154030096322843537796774 = ((6308060192645687075593548 : ℕ) : ZMod 6308060192645687075593549) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6308060192645687075593549 - 1) / 3 = 2102686730881895691864516 from by norm_num]
      have h2 : (7 : ZMod 6308060192645687075593549) ^ 2102686730881895691864516 = ((4272097075102691989399940 : ℕ) : ZMod 6308060192645687075593549) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6308060192645687075593549 - 1) / 23 = 274263486636769003286676 from by norm_num]
      have h2 : (7 : ZMod 6308060192645687075593549) ^ 274263486636769003286676 = ((5357925822067619588471117 : ℕ) : ZMod 6308060192645687075593549) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6308060192645687075593549 - 1) / 31 = 203485812665989905664308 from by norm_num]
      have h2 : (7 : ZMod 6308060192645687075593549) ^ 203485812665989905664308 = ((2826630659820292541712099 : ℕ) : ZMod 6308060192645687075593549) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6308060192645687075593549 - 1) / 6101 = 1033938730150088030748 from by norm_num]
      have h2 : (7 : ZMod 6308060192645687075593549) ^ 1033938730150088030748 = ((792824490007356699425353 : ℕ) : ZMod 6308060192645687075593549) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_130372757).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6308060192645687075593549 - 1) / 130372757 = 48384803219630364 from by norm_num]
      have h2 : (7 : ZMod 6308060192645687075593549) ^ 48384803219630364 = ((146876516950918980799843 : ℕ) : ZMod 6308060192645687075593549) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_308969723).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6308060192645687075593549 - 1) / 308969723 = 20416434760650276 from by norm_num]
      have h2 : (7 : ZMod 6308060192645687075593549) ^ 20416434760650276 = ((1246363023066958497588376 : ℕ) : ZMod 6308060192645687075593549) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3219373317019287939398178066320988767 : Nat.Prime 3219373317019287939398178066320988767 := by
  refine lucas_primality 3219373317019287939398178066320988767 (5 : ZMod 3219373317019287939398178066320988767) ?_ (fun q hq hd => ?_)
  · rw [show 3219373317019287939398178066320988767 - 1 = 3219373317019287939398178066320988766 from by norm_num]
    reduce_mod_char
  · have e : 3219373317019287939398178066320988767 - 1 = [2 ^ 1, 509 ^ 1, 501334663 ^ 1, 6308060192645687075593549 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3219373317019287939398178066320988767 - 1) / 2 = 1609686658509643969699089033160494383 from by norm_num]
      have h2 : (5 : ZMod 3219373317019287939398178066320988767) ^ 1609686658509643969699089033160494383 = ((3219373317019287939398178066320988766 : ℕ) : ZMod 3219373317019287939398178066320988767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3219373317019287939398178066320988767 - 1) / 509 = 6324898461727481216892294825777974 from by norm_num]
      have h2 : (5 : ZMod 3219373317019287939398178066320988767) ^ 6324898461727481216892294825777974 = ((2380574666665828758048761889633063651 : ℕ) : ZMod 3219373317019287939398178066320988767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_501334663).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3219373317019287939398178066320988767 - 1) / 501334663 = 6421605276113309442954232882 from by norm_num]
      have h2 : (5 : ZMod 3219373317019287939398178066320988767) ^ 6421605276113309442954232882 = ((3197525227721984883687333174311936905 : ℕ) : ZMod 3219373317019287939398178066320988767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6308060192645687075593549).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3219373317019287939398178066320988767 - 1) / 6308060192645687075593549 = 510358686934 from by norm_num]
      have h2 : (5 : ZMod 3219373317019287939398178066320988767) ^ 510358686934 = ((2264337247064133090717300467271069263 : ℕ) : ZMod 3219373317019287939398178066320988767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_439528161479375305214275658682539312403443 : Nat.Prime 439528161479375305214275658682539312403443 := by
  refine lucas_primality 439528161479375305214275658682539312403443 (2 : ZMod 439528161479375305214275658682539312403443) ?_ (fun q hq hd => ?_)
  · rw [show 439528161479375305214275658682539312403443 - 1 = 439528161479375305214275658682539312403442 from by norm_num]
    reduce_mod_char
  · have e : 439528161479375305214275658682539312403443 - 1 = [2 ^ 1, 13 ^ 1, 59 ^ 1, 89 ^ 1, 3219373317019287939398178066320988767 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (439528161479375305214275658682539312403443 - 1) / 2 = 219764080739687652607137829341269656201721 from by norm_num]
      have h2 : (2 : ZMod 439528161479375305214275658682539312403443) ^ 219764080739687652607137829341269656201721 = ((439528161479375305214275658682539312403442 : ℕ) : ZMod 439528161479375305214275658682539312403443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (439528161479375305214275658682539312403443 - 1) / 13 = 33809858575336561939559666052503024031034 from by norm_num]
      have h2 : (2 : ZMod 439528161479375305214275658682539312403443) ^ 33809858575336561939559666052503024031034 = ((317045797820832918554480189444167485250462 : ℕ) : ZMod 439528161479375305214275658682539312403443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (439528161479375305214275658682539312403443 - 1) / 59 = 7449629855582632291767384045466768006838 from by norm_num]
      have h2 : (2 : ZMod 439528161479375305214275658682539312403443) ^ 7449629855582632291767384045466768006838 = ((421676062422107927482314422935558363444756 : ℕ) : ZMod 439528161479375305214275658682539312403443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (439528161479375305214275658682539312403443 - 1) / 89 = 4938518668307587699036805153736396768578 from by norm_num]
      have h2 : (2 : ZMod 439528161479375305214275658682539312403443) ^ 4938518668307587699036805153736396768578 = ((369003110555876903008373167917213016684025 : ℕ) : ZMod 439528161479375305214275658682539312403443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3219373317019287939398178066320988767).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (439528161479375305214275658682539312403443 - 1) / 3219373317019287939398178066320988767 = 136526 from by norm_num]
      have h2 : (2 : ZMod 439528161479375305214275658682539312403443) ^ 136526 = ((140719541652196244665724967580129188463225 : ℕ) : ZMod 439528161479375305214275658682539312403443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1842783354049795450301 : Nat.Prime 1842783354049795450301 := by
  refine lucas_primality 1842783354049795450301 (3 : ZMod 1842783354049795450301) ?_ (fun q hq hd => ?_)
  · rw [show 1842783354049795450301 - 1 = 1842783354049795450300 from by norm_num]
    reduce_mod_char
  · have e : 1842783354049795450301 - 1 = [2 ^ 2, 5 ^ 2, 7 ^ 1, 17 ^ 1, 4651 ^ 1, 6277 ^ 1, 53507 ^ 1, 99133 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1842783354049795450301 - 1) / 2 = 921391677024897725150 from by norm_num]
      have h2 : (3 : ZMod 1842783354049795450301) ^ 921391677024897725150 = ((1842783354049795450300 : ℕ) : ZMod 1842783354049795450301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1842783354049795450301 - 1) / 5 = 368556670809959090060 from by norm_num]
      have h2 : (3 : ZMod 1842783354049795450301) ^ 368556670809959090060 = ((708688618698893714004 : ℕ) : ZMod 1842783354049795450301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1842783354049795450301 - 1) / 7 = 263254764864256492900 from by norm_num]
      have h2 : (3 : ZMod 1842783354049795450301) ^ 263254764864256492900 = ((1523454009251424475956 : ℕ) : ZMod 1842783354049795450301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1842783354049795450301 - 1) / 17 = 108399020826458555900 from by norm_num]
      have h2 : (3 : ZMod 1842783354049795450301) ^ 108399020826458555900 = ((1506120746359970182679 : ℕ) : ZMod 1842783354049795450301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1842783354049795450301 - 1) / 4651 = 396212288550805300 from by norm_num]
      have h2 : (3 : ZMod 1842783354049795450301) ^ 396212288550805300 = ((430166911253790958843 : ℕ) : ZMod 1842783354049795450301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1842783354049795450301 - 1) / 6277 = 293577083646613900 from by norm_num]
      have h2 : (3 : ZMod 1842783354049795450301) ^ 293577083646613900 = ((1193006761147800913038 : ℕ) : ZMod 1842783354049795450301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1842783354049795450301 - 1) / 53507 = 34440042500042900 from by norm_num]
      have h2 : (3 : ZMod 1842783354049795450301) ^ 34440042500042900 = ((1807681042396096386173 : ℕ) : ZMod 1842783354049795450301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1842783354049795450301 - 1) / 99133 = 18589000171989100 from by norm_num]
      have h2 : (3 : ZMod 1842783354049795450301) ^ 18589000171989100 = ((1045401344469698652967 : ℕ) : ZMod 1842783354049795450301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_921391677024897725150501 : Nat.Prime 921391677024897725150501 := by
  refine lucas_primality 921391677024897725150501 (2 : ZMod 921391677024897725150501) ?_ (fun q hq hd => ?_)
  · rw [show 921391677024897725150501 - 1 = 921391677024897725150500 from by norm_num]
    reduce_mod_char
  · have e : 921391677024897725150501 - 1 = [2 ^ 2, 5 ^ 3, 1842783354049795450301 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (921391677024897725150501 - 1) / 2 = 460695838512448862575250 from by norm_num]
      have h2 : (2 : ZMod 921391677024897725150501) ^ 460695838512448862575250 = ((921391677024897725150500 : ℕ) : ZMod 921391677024897725150501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (921391677024897725150501 - 1) / 5 = 184278335404979545030100 from by norm_num]
      have h2 : (2 : ZMod 921391677024897725150501) ^ 184278335404979545030100 = ((406237403622518487254023 : ℕ) : ZMod 921391677024897725150501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1842783354049795450301).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (921391677024897725150501 - 1) / 1842783354049795450301 = 500 from by norm_num]
      have h2 : (2 : ZMod 921391677024897725150501) ^ 500 = ((869201996813111670537539 : ℕ) : ZMod 921391677024897725150501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2320521589583519038984190368845334252032614658313846668819967944423391 : Nat.Prime 2320521589583519038984190368845334252032614658313846668819967944423391 := by
  refine lucas_primality 2320521589583519038984190368845334252032614658313846668819967944423391 (6 : ZMod 2320521589583519038984190368845334252032614658313846668819967944423391) ?_ (fun q hq hd => ?_)
  · rw [show 2320521589583519038984190368845334252032614658313846668819967944423391 - 1 = 2320521589583519038984190368845334252032614658313846668819967944423390 from by norm_num]
    reduce_mod_char
  · have e : 2320521589583519038984190368845334252032614658313846668819967944423391 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 191 ^ 1, 921391677024897725150501 ^ 1, 439528161479375305214275658682539312403443 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2320521589583519038984190368845334252032614658313846668819967944423391 - 1) / 2 = 1160260794791759519492095184422667126016307329156923334409983972211695 from by norm_num]
      have h2 : (6 : ZMod 2320521589583519038984190368845334252032614658313846668819967944423391) ^ 1160260794791759519492095184422667126016307329156923334409983972211695 = ((2320521589583519038984190368845334252032614658313846668819967944423390 : ℕ) : ZMod 2320521589583519038984190368845334252032614658313846668819967944423391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2320521589583519038984190368845334252032614658313846668819967944423391 - 1) / 3 = 773507196527839679661396789615111417344204886104615556273322648141130 from by norm_num]
      have h2 : (6 : ZMod 2320521589583519038984190368845334252032614658313846668819967944423391) ^ 773507196527839679661396789615111417344204886104615556273322648141130 = ((34845291468767625091107696515053181827726604867242516787848018037397 : ℕ) : ZMod 2320521589583519038984190368845334252032614658313846668819967944423391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2320521589583519038984190368845334252032614658313846668819967944423391 - 1) / 5 = 464104317916703807796838073769066850406522931662769333763993588884678 from by norm_num]
      have h2 : (6 : ZMod 2320521589583519038984190368845334252032614658313846668819967944423391) ^ 464104317916703807796838073769066850406522931662769333763993588884678 = ((2133122171461184549697834674588548339285084993711222402333145845343288 : ℕ) : ZMod 2320521589583519038984190368845334252032614658313846668819967944423391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2320521589583519038984190368845334252032614658313846668819967944423391 - 1) / 191 = 12149327694154549942325604025368242157238820200596055857696167248290 from by norm_num]
      have h2 : (6 : ZMod 2320521589583519038984190368845334252032614658313846668819967944423391) ^ 12149327694154549942325604025368242157238820200596055857696167248290 = ((961260608039644274227645776030652153264285986977931034216577746623551 : ℕ) : ZMod 2320521589583519038984190368845334252032614658313846668819967944423391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_921391677024897725150501).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2320521589583519038984190368845334252032614658313846668819967944423391 - 1) / 921391677024897725150501 = 2518496365276820498877799524250950260071728390 from by norm_num]
      have h2 : (6 : ZMod 2320521589583519038984190368845334252032614658313846668819967944423391) ^ 2518496365276820498877799524250950260071728390 = ((316030618704522090632483654829568120189049895491972550220453946813189 : ℕ) : ZMod 2320521589583519038984190368845334252032614658313846668819967944423391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_439528161479375305214275658682539312403443).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2320521589583519038984190368845334252032614658313846668819967944423391 - 1) / 439528161479375305214275658682539312403443 = 5279574309352663965112370730 from by norm_num]
      have h2 : (6 : ZMod 2320521589583519038984190368845334252032614658313846668819967944423391) ^ 5279574309352663965112370730 = ((666279494050093723476912458138247281936509045058318207954902564672898 : ℕ) : ZMod 2320521589583519038984190368845334252032614658313846668819967944423391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4683634048176303989 : Nat.Prime 4683634048176303989 := by
  refine lucas_primality 4683634048176303989 (2 : ZMod 4683634048176303989) ?_ (fun q hq hd => ?_)
  · rw [show 4683634048176303989 - 1 = 4683634048176303988 from by norm_num]
    reduce_mod_char
  · have e : 4683634048176303989 - 1 = [2 ^ 2, 89 ^ 1, 97231 ^ 1, 110749 ^ 1, 1221767 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4683634048176303989 - 1) / 2 = 2341817024088151994 from by norm_num]
      have h2 : (2 : ZMod 4683634048176303989) ^ 2341817024088151994 = ((4683634048176303988 : ℕ) : ZMod 4683634048176303989) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4683634048176303989 - 1) / 89 = 52625101664902292 from by norm_num]
      have h2 : (2 : ZMod 4683634048176303989) ^ 52625101664902292 = ((1631637788720999754 : ℕ) : ZMod 4683634048176303989) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4683634048176303989 - 1) / 97231 = 48170172559948 from by norm_num]
      have h2 : (2 : ZMod 4683634048176303989) ^ 48170172559948 = ((1817075818199838575 : ℕ) : ZMod 4683634048176303989) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4683634048176303989 - 1) / 110749 = 42290531275012 from by norm_num]
      have h2 : (2 : ZMod 4683634048176303989) ^ 42290531275012 = ((1215266909215635226 : ℕ) : ZMod 4683634048176303989) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4683634048176303989 - 1) / 1221767 = 3833492022764 from by norm_num]
      have h2 : (2 : ZMod 4683634048176303989) ^ 3833492022764 = ((200634575576819713 : ℕ) : ZMod 4683634048176303989) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 : Nat.Prime 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 := by
  refine lucas_primality 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 (3 : ZMod 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733) ?_ (fun q hq hd => ?_)
  · rw [show 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 - 1 = 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113732 from by norm_num]
    reduce_mod_char
  · have e : 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 - 1 = [2 ^ 2, 467 ^ 1, 4683634048176303989 ^ 1, 2320521589583519038984190368845334252032614658313846668819967944423391 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 - 1) / 2 = 10151154647352465561299300552837154234287637828608556060177570816541747072950473157085056866 from by norm_num]
      have h2 : (3 : ZMod 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733) ^ 10151154647352465561299300552837154234287637828608556060177570816541747072950473157085056866 = ((20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113732 : ℕ) : ZMod 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 - 1) / 467 = 43473895706006276493787154401872180874893523891257199401188740113669152346682968552826796 from by norm_num]
      have h2 : (3 : ZMod 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733) ^ 43473895706006276493787154401872180874893523891257199401188740113669152346682968552826796 = ((2258173642991947512517565000163218437494927750059609186913495131252364407993236841851753649 : ℕ) : ZMod 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4683634048176303989).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 - 1) / 4683634048176303989 = 4334734329342013564822467609003084382796924181730265577355700120182894388 from by norm_num]
      have h2 : (3 : ZMod 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733) ^ 4334734329342013564822467609003084382796924181730265577355700120182894388 = ((9604806913197385640053953750385161764416484704910225208481083072492808022396027788872554617 : ℕ) : ZMod 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2320521589583519038984190368845334252032614658313846668819967944423391).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 - 1) / 2320521589583519038984190368845334252032614658313846668819967944423391 = 8749028401993335851452 from by norm_num]
      have h2 : (3 : ZMod 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733) ^ 8749028401993335851452 = ((1389037705826752471821218818726800258482032668017053165548300352761701299222503454635650818 : ℕ) : ZMod 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9148411421 : Nat.Prime 9148411421 := by
  refine lucas_primality 9148411421 (3 : ZMod 9148411421) ?_ (fun q hq hd => ?_)
  · rw [show 9148411421 - 1 = 9148411420 from by norm_num]
    reduce_mod_char
  · have e : 9148411421 - 1 = [2 ^ 2, 5 ^ 1, 109 ^ 1, 479 ^ 1, 8761 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9148411421 - 1) / 2 = 4574205710 from by norm_num]
      have h2 : (3 : ZMod 9148411421) ^ 4574205710 = ((9148411420 : ℕ) : ZMod 9148411421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9148411421 - 1) / 5 = 1829682284 from by norm_num]
      have h2 : (3 : ZMod 9148411421) ^ 1829682284 = ((9116604650 : ℕ) : ZMod 9148411421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9148411421 - 1) / 109 = 83930380 from by norm_num]
      have h2 : (3 : ZMod 9148411421) ^ 83930380 = ((5016684078 : ℕ) : ZMod 9148411421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9148411421 - 1) / 479 = 19098980 from by norm_num]
      have h2 : (3 : ZMod 9148411421) ^ 19098980 = ((2610322861 : ℕ) : ZMod 9148411421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9148411421 - 1) / 8761 = 1044220 from by norm_num]
      have h2 : (3 : ZMod 9148411421) ^ 1044220 = ((4673604321 : ℕ) : ZMod 9148411421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_382638557753 : Nat.Prime 382638557753 := by
  refine lucas_primality 382638557753 (3 : ZMod 382638557753) ?_ (fun q hq hd => ?_)
  · rw [show 382638557753 - 1 = 382638557752 from by norm_num]
    reduce_mod_char
  · have e : 382638557753 - 1 = [2 ^ 3, 11 ^ 1, 17 ^ 1, 1009 ^ 1, 253493 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (382638557753 - 1) / 2 = 191319278876 from by norm_num]
      have h2 : (3 : ZMod 382638557753) ^ 191319278876 = ((382638557752 : ℕ) : ZMod 382638557753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (382638557753 - 1) / 11 = 34785323432 from by norm_num]
      have h2 : (3 : ZMod 382638557753) ^ 34785323432 = ((295313509791 : ℕ) : ZMod 382638557753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (382638557753 - 1) / 17 = 22508150456 from by norm_num]
      have h2 : (3 : ZMod 382638557753) ^ 22508150456 = ((111921739816 : ℕ) : ZMod 382638557753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (382638557753 - 1) / 1009 = 379225528 from by norm_num]
      have h2 : (3 : ZMod 382638557753) ^ 379225528 = ((237460778186 : ℕ) : ZMod 382638557753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (382638557753 - 1) / 253493 = 1509464 from by norm_num]
      have h2 : (3 : ZMod 382638557753) ^ 1509464 = ((86923172203 : ℕ) : ZMod 382638557753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_765277115507 : Nat.Prime 765277115507 := by
  refine lucas_primality 765277115507 (2 : ZMod 765277115507) ?_ (fun q hq hd => ?_)
  · rw [show 765277115507 - 1 = 765277115506 from by norm_num]
    reduce_mod_char
  · have e : 765277115507 - 1 = [2 ^ 1, 382638557753 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (765277115507 - 1) / 2 = 382638557753 from by norm_num]
      have h2 : (2 : ZMod 765277115507) ^ 382638557753 = ((765277115506 : ℕ) : ZMod 765277115507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_382638557753).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (765277115507 - 1) / 382638557753 = 2 from by norm_num]
      have h2 : (2 : ZMod 765277115507) ^ 2 = ((4 : ℕ) : ZMod 765277115507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_29325513271841158911701 : Nat.Prime 29325513271841158911701 := by
  refine lucas_primality 29325513271841158911701 (3 : ZMod 29325513271841158911701) ?_ (fun q hq hd => ?_)
  · rw [show 29325513271841158911701 - 1 = 29325513271841158911700 from by norm_num]
    reduce_mod_char
  · have e : 29325513271841158911701 - 1 = [2 ^ 2, 5 ^ 2, 7 ^ 1, 179 ^ 1, 521 ^ 1, 587 ^ 1, 765277115507 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29325513271841158911701 - 1) / 2 = 14662756635920579455850 from by norm_num]
      have h2 : (3 : ZMod 29325513271841158911701) ^ 14662756635920579455850 = ((29325513271841158911700 : ℕ) : ZMod 29325513271841158911701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29325513271841158911701 - 1) / 5 = 5865102654368231782340 from by norm_num]
      have h2 : (3 : ZMod 29325513271841158911701) ^ 5865102654368231782340 = ((19405539952600422203291 : ℕ) : ZMod 29325513271841158911701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29325513271841158911701 - 1) / 7 = 4189359038834451273100 from by norm_num]
      have h2 : (3 : ZMod 29325513271841158911701) ^ 4189359038834451273100 = ((19723973492340568176229 : ℕ) : ZMod 29325513271841158911701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29325513271841158911701 - 1) / 179 = 163829683082911502300 from by norm_num]
      have h2 : (3 : ZMod 29325513271841158911701) ^ 163829683082911502300 = ((456417842594726389934 : ℕ) : ZMod 29325513271841158911701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29325513271841158911701 - 1) / 521 = 56286973650366907700 from by norm_num]
      have h2 : (3 : ZMod 29325513271841158911701) ^ 56286973650366907700 = ((16906837182232005595734 : ℕ) : ZMod 29325513271841158911701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29325513271841158911701 - 1) / 587 = 49958284960547119100 from by norm_num]
      have h2 : (3 : ZMod 29325513271841158911701) ^ 49958284960547119100 = ((2455676238030894682301 : ℕ) : ZMod 29325513271841158911701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_765277115507).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29325513271841158911701 - 1) / 765277115507 = 38320123100 from by norm_num]
      have h2 : (3 : ZMod 29325513271841158911701) ^ 38320123100 = ((264221703827335375620 : ℕ) : ZMod 29325513271841158911701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8352693761 : Nat.Prime 8352693761 := by
  refine lucas_primality 8352693761 (3 : ZMod 8352693761) ?_ (fun q hq hd => ?_)
  · rw [show 8352693761 - 1 = 8352693760 from by norm_num]
    reduce_mod_char
  · have e : 8352693761 - 1 = [2 ^ 9, 5 ^ 1, 37 ^ 1, 163 ^ 1, 541 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8352693761 - 1) / 2 = 4176346880 from by norm_num]
      have h2 : (3 : ZMod 8352693761) ^ 4176346880 = ((8352693760 : ℕ) : ZMod 8352693761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8352693761 - 1) / 5 = 1670538752 from by norm_num]
      have h2 : (3 : ZMod 8352693761) ^ 1670538752 = ((7788708475 : ℕ) : ZMod 8352693761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8352693761 - 1) / 37 = 225748480 from by norm_num]
      have h2 : (3 : ZMod 8352693761) ^ 225748480 = ((3794411764 : ℕ) : ZMod 8352693761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8352693761 - 1) / 163 = 51243520 from by norm_num]
      have h2 : (3 : ZMod 8352693761) ^ 51243520 = ((4915362271 : ℕ) : ZMod 8352693761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8352693761 - 1) / 541 = 15439360 from by norm_num]
      have h2 : (3 : ZMod 8352693761) ^ 15439360 = ((6437589519 : ℕ) : ZMod 8352693761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_67887077 : Nat.Prime 67887077 := by
  refine lucas_primality 67887077 (3 : ZMod 67887077) ?_ (fun q hq hd => ?_)
  · rw [show 67887077 - 1 = 67887076 from by norm_num]
    reduce_mod_char
  · have e : 67887077 - 1 = [2 ^ 2, 19 ^ 1, 23 ^ 1, 71 ^ 1, 547 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67887077 - 1) / 2 = 33943538 from by norm_num]
      have h2 : (3 : ZMod 67887077) ^ 33943538 = ((67887076 : ℕ) : ZMod 67887077) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67887077 - 1) / 19 = 3573004 from by norm_num]
      have h2 : (3 : ZMod 67887077) ^ 3573004 = ((3866067 : ℕ) : ZMod 67887077) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67887077 - 1) / 23 = 2951612 from by norm_num]
      have h2 : (3 : ZMod 67887077) ^ 2951612 = ((33630979 : ℕ) : ZMod 67887077) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67887077 - 1) / 71 = 956156 from by norm_num]
      have h2 : (3 : ZMod 67887077) ^ 956156 = ((17182978 : ℕ) : ZMod 67887077) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67887077 - 1) / 547 = 124108 from by norm_num]
      have h2 : (3 : ZMod 67887077) ^ 124108 = ((36813233 : ℕ) : ZMod 67887077) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_45232564075409 : Nat.Prime 45232564075409 := by
  refine lucas_primality 45232564075409 (3 : ZMod 45232564075409) ?_ (fun q hq hd => ?_)
  · rw [show 45232564075409 - 1 = 45232564075408 from by norm_num]
    reduce_mod_char
  · have e : 45232564075409 - 1 = [2 ^ 4, 337 ^ 1, 547 ^ 1, 15336067 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45232564075409 - 1) / 2 = 22616282037704 from by norm_num]
      have h2 : (3 : ZMod 45232564075409) ^ 22616282037704 = ((45232564075408 : ℕ) : ZMod 45232564075409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45232564075409 - 1) / 337 = 134221258384 from by norm_num]
      have h2 : (3 : ZMod 45232564075409) ^ 134221258384 = ((36831073973125 : ℕ) : ZMod 45232564075409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45232564075409 - 1) / 547 = 82692073264 from by norm_num]
      have h2 : (3 : ZMod 45232564075409) ^ 82692073264 = ((44738258393100 : ℕ) : ZMod 45232564075409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45232564075409 - 1) / 15336067 = 2949424 from by norm_num]
      have h2 : (3 : ZMod 45232564075409) ^ 2949424 = ((41376132144514 : ℕ) : ZMod 45232564075409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_91441702997 : Nat.Prime 91441702997 := by
  refine lucas_primality 91441702997 (3 : ZMod 91441702997) ?_ (fun q hq hd => ?_)
  · rw [show 91441702997 - 1 = 91441702996 from by norm_num]
    reduce_mod_char
  · have e : 91441702997 - 1 = [2 ^ 2, 7 ^ 2, 101 ^ 1, 557 ^ 1, 8293 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91441702997 - 1) / 2 = 45720851498 from by norm_num]
      have h2 : (3 : ZMod 91441702997) ^ 45720851498 = ((91441702996 : ℕ) : ZMod 91441702997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91441702997 - 1) / 7 = 13063100428 from by norm_num]
      have h2 : (3 : ZMod 91441702997) ^ 13063100428 = ((19108156034 : ℕ) : ZMod 91441702997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91441702997 - 1) / 101 = 905363396 from by norm_num]
      have h2 : (3 : ZMod 91441702997) ^ 905363396 = ((52405803552 : ℕ) : ZMod 91441702997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91441702997 - 1) / 557 = 164168228 from by norm_num]
      have h2 : (3 : ZMod 91441702997) ^ 164168228 = ((32390031896 : ℕ) : ZMod 91441702997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91441702997 - 1) / 8293 = 11026372 from by norm_num]
      have h2 : (3 : ZMod 91441702997) ^ 11026372 = ((25935944076 : ℕ) : ZMod 91441702997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_133489553 : Nat.Prime 133489553 := by
  refine lucas_primality 133489553 (3 : ZMod 133489553) ?_ (fun q hq hd => ?_)
  · rw [show 133489553 - 1 = 133489552 from by norm_num]
    reduce_mod_char
  · have e : 133489553 - 1 = [2 ^ 4, 7 ^ 1, 29 ^ 1, 73 ^ 1, 563 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133489553 - 1) / 2 = 66744776 from by norm_num]
      have h2 : (3 : ZMod 133489553) ^ 66744776 = ((133489552 : ℕ) : ZMod 133489553) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133489553 - 1) / 7 = 19069936 from by norm_num]
      have h2 : (3 : ZMod 133489553) ^ 19069936 = ((93254018 : ℕ) : ZMod 133489553) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133489553 - 1) / 29 = 4603088 from by norm_num]
      have h2 : (3 : ZMod 133489553) ^ 4603088 = ((44558667 : ℕ) : ZMod 133489553) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133489553 - 1) / 73 = 1828624 from by norm_num]
      have h2 : (3 : ZMod 133489553) ^ 1828624 = ((28390268 : ℕ) : ZMod 133489553) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133489553 - 1) / 563 = 237104 from by norm_num]
      have h2 : (3 : ZMod 133489553) ^ 237104 = ((45623633 : ℕ) : ZMod 133489553) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_94600997 : Nat.Prime 94600997 := by
  refine lucas_primality 94600997 (3 : ZMod 94600997) ?_ (fun q hq hd => ?_)
  · rw [show 94600997 - 1 = 94600996 from by norm_num]
    reduce_mod_char
  · have e : 94600997 - 1 = [2 ^ 2, 7 ^ 1, 61 ^ 1, 97 ^ 1, 571 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94600997 - 1) / 2 = 47300498 from by norm_num]
      have h2 : (3 : ZMod 94600997) ^ 47300498 = ((94600996 : ℕ) : ZMod 94600997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94600997 - 1) / 7 = 13514428 from by norm_num]
      have h2 : (3 : ZMod 94600997) ^ 13514428 = ((72213305 : ℕ) : ZMod 94600997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94600997 - 1) / 61 = 1550836 from by norm_num]
      have h2 : (3 : ZMod 94600997) ^ 1550836 = ((3267657 : ℕ) : ZMod 94600997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94600997 - 1) / 97 = 975268 from by norm_num]
      have h2 : (3 : ZMod 94600997) ^ 975268 = ((93842034 : ℕ) : ZMod 94600997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94600997 - 1) / 571 = 165676 from by norm_num]
      have h2 : (3 : ZMod 94600997) ^ 165676 = ((76480913 : ℕ) : ZMod 94600997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_92936237 : Nat.Prime 92936237 := by
  refine lucas_primality 92936237 (3 : ZMod 92936237) ?_ (fun q hq hd => ?_)
  · rw [show 92936237 - 1 = 92936236 from by norm_num]
    reduce_mod_char
  · have e : 92936237 - 1 = [2 ^ 2, 67 ^ 1, 577 ^ 1, 601 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92936237 - 1) / 2 = 46468118 from by norm_num]
      have h2 : (3 : ZMod 92936237) ^ 46468118 = ((92936236 : ℕ) : ZMod 92936237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92936237 - 1) / 67 = 1387108 from by norm_num]
      have h2 : (3 : ZMod 92936237) ^ 1387108 = ((45267918 : ℕ) : ZMod 92936237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92936237 - 1) / 577 = 161068 from by norm_num]
      have h2 : (3 : ZMod 92936237) ^ 161068 = ((80386319 : ℕ) : ZMod 92936237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92936237 - 1) / 601 = 154636 from by norm_num]
      have h2 : (3 : ZMod 92936237) ^ 154636 = ((25601589 : ℕ) : ZMod 92936237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2434616217281 : Nat.Prime 2434616217281 := by
  refine lucas_primality 2434616217281 (3 : ZMod 2434616217281) ?_ (fun q hq hd => ?_)
  · rw [show 2434616217281 - 1 = 2434616217280 from by norm_num]
    reduce_mod_char
  · have e : 2434616217281 - 1 = [2 ^ 6, 5 ^ 1, 13 ^ 2, 271 ^ 1, 283 ^ 1, 587 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2434616217281 - 1) / 2 = 1217308108640 from by norm_num]
      have h2 : (3 : ZMod 2434616217281) ^ 1217308108640 = ((2434616217280 : ℕ) : ZMod 2434616217281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2434616217281 - 1) / 5 = 486923243456 from by norm_num]
      have h2 : (3 : ZMod 2434616217281) ^ 486923243456 = ((943152480144 : ℕ) : ZMod 2434616217281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2434616217281 - 1) / 13 = 187278170560 from by norm_num]
      have h2 : (3 : ZMod 2434616217281) ^ 187278170560 = ((2407508160006 : ℕ) : ZMod 2434616217281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2434616217281 - 1) / 271 = 8983823680 from by norm_num]
      have h2 : (3 : ZMod 2434616217281) ^ 8983823680 = ((228024206167 : ℕ) : ZMod 2434616217281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2434616217281 - 1) / 283 = 8602884160 from by norm_num]
      have h2 : (3 : ZMod 2434616217281) ^ 8602884160 = ((1815647481744 : ℕ) : ZMod 2434616217281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2434616217281 - 1) / 587 = 4147557440 from by norm_num]
      have h2 : (3 : ZMod 2434616217281) ^ 4147557440 = ((1763193794389 : ℕ) : ZMod 2434616217281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8121518879 : Nat.Prime 8121518879 := by
  refine lucas_primality 8121518879 (11 : ZMod 8121518879) ?_ (fun q hq hd => ?_)
  · rw [show 8121518879 - 1 = 8121518878 from by norm_num]
    reduce_mod_char
  · have e : 8121518879 - 1 = [2 ^ 1, 11 ^ 1, 19 ^ 1, 47 ^ 1, 101 ^ 1, 4093 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8121518879 - 1) / 2 = 4060759439 from by norm_num]
      have h2 : (11 : ZMod 8121518879) ^ 4060759439 = ((8121518878 : ℕ) : ZMod 8121518879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8121518879 - 1) / 11 = 738319898 from by norm_num]
      have h2 : (11 : ZMod 8121518879) ^ 738319898 = ((4314710393 : ℕ) : ZMod 8121518879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8121518879 - 1) / 19 = 427448362 from by norm_num]
      have h2 : (11 : ZMod 8121518879) ^ 427448362 = ((633664249 : ℕ) : ZMod 8121518879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8121518879 - 1) / 47 = 172798274 from by norm_num]
      have h2 : (11 : ZMod 8121518879) ^ 172798274 = ((2016403995 : ℕ) : ZMod 8121518879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8121518879 - 1) / 101 = 80411078 from by norm_num]
      have h2 : (11 : ZMod 8121518879) ^ 80411078 = ((2593274617 : ℕ) : ZMod 8121518879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8121518879 - 1) / 4093 = 1984246 from by norm_num]
      have h2 : (11 : ZMod 8121518879) ^ 1984246 = ((4868505511 : ℕ) : ZMod 8121518879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_679048043521919 : Nat.Prime 679048043521919 := by
  refine lucas_primality 679048043521919 (7 : ZMod 679048043521919) ?_ (fun q hq hd => ?_)
  · rw [show 679048043521919 - 1 = 679048043521918 from by norm_num]
    reduce_mod_char
  · have e : 679048043521919 - 1 = [2 ^ 1, 7 ^ 2, 43 ^ 1, 228793 ^ 1, 704309 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (679048043521919 - 1) / 2 = 339524021760959 from by norm_num]
      have h2 : (7 : ZMod 679048043521919) ^ 339524021760959 = ((679048043521918 : ℕ) : ZMod 679048043521919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (679048043521919 - 1) / 7 = 97006863360274 from by norm_num]
      have h2 : (7 : ZMod 679048043521919) ^ 97006863360274 = ((371878203296923 : ℕ) : ZMod 679048043521919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (679048043521919 - 1) / 43 = 15791814965626 from by norm_num]
      have h2 : (7 : ZMod 679048043521919) ^ 15791814965626 = ((414210660559753 : ℕ) : ZMod 679048043521919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (679048043521919 - 1) / 228793 = 2967958126 from by norm_num]
      have h2 : (7 : ZMod 679048043521919) ^ 2967958126 = ((428768315433382 : ℕ) : ZMod 679048043521919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (679048043521919 - 1) / 704309 = 964133702 from by norm_num]
      have h2 : (7 : ZMod 679048043521919) ^ 964133702 = ((126245988325635 : ℕ) : ZMod 679048043521919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_71737507 : Nat.Prime 71737507 := by
  refine lucas_primality 71737507 (2 : ZMod 71737507) ?_ (fun q hq hd => ?_)
  · rw [show 71737507 - 1 = 71737506 from by norm_num]
    reduce_mod_char
  · have e : 71737507 - 1 = [2 ^ 1, 3 ^ 2, 23 ^ 1, 241 ^ 1, 719 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71737507 - 1) / 2 = 35868753 from by norm_num]
      have h2 : (2 : ZMod 71737507) ^ 35868753 = ((71737506 : ℕ) : ZMod 71737507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71737507 - 1) / 3 = 23912502 from by norm_num]
      have h2 : (2 : ZMod 71737507) ^ 23912502 = ((16872710 : ℕ) : ZMod 71737507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71737507 - 1) / 23 = 3119022 from by norm_num]
      have h2 : (2 : ZMod 71737507) ^ 3119022 = ((18546656 : ℕ) : ZMod 71737507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71737507 - 1) / 241 = 297666 from by norm_num]
      have h2 : (2 : ZMod 71737507) ^ 297666 = ((60299061 : ℕ) : ZMod 71737507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71737507 - 1) / 719 = 99774 from by norm_num]
      have h2 : (2 : ZMod 71737507) ^ 99774 = ((29348781 : ℕ) : ZMod 71737507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6312900617 : Nat.Prime 6312900617 := by
  refine lucas_primality 6312900617 (3 : ZMod 6312900617) ?_ (fun q hq hd => ?_)
  · rw [show 6312900617 - 1 = 6312900616 from by norm_num]
    reduce_mod_char
  · have e : 6312900617 - 1 = [2 ^ 3, 11 ^ 1, 71737507 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6312900617 - 1) / 2 = 3156450308 from by norm_num]
      have h2 : (3 : ZMod 6312900617) ^ 3156450308 = ((6312900616 : ℕ) : ZMod 6312900617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6312900617 - 1) / 11 = 573900056 from by norm_num]
      have h2 : (3 : ZMod 6312900617) ^ 573900056 = ((4998260144 : ℕ) : ZMod 6312900617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_71737507).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6312900617 - 1) / 71737507 = 88 from by norm_num]
      have h2 : (3 : ZMod 6312900617) ^ 88 = ((2144389301 : ℕ) : ZMod 6312900617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_219006580043908471 : Nat.Prime 219006580043908471 := by
  refine lucas_primality 219006580043908471 (3 : ZMod 219006580043908471) ?_ (fun q hq hd => ?_)
  · rw [show 219006580043908471 - 1 = 219006580043908470 from by norm_num]
    reduce_mod_char
  · have e : 219006580043908471 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 11 ^ 2, 19 ^ 1, 503 ^ 1, 6312900617 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219006580043908471 - 1) / 2 = 109503290021954235 from by norm_num]
      have h2 : (3 : ZMod 219006580043908471) ^ 109503290021954235 = ((219006580043908470 : ℕ) : ZMod 219006580043908471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219006580043908471 - 1) / 3 = 73002193347969490 from by norm_num]
      have h2 : (3 : ZMod 219006580043908471) ^ 73002193347969490 = ((174768874465710542 : ℕ) : ZMod 219006580043908471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219006580043908471 - 1) / 5 = 43801316008781694 from by norm_num]
      have h2 : (3 : ZMod 219006580043908471) ^ 43801316008781694 = ((206992689134733556 : ℕ) : ZMod 219006580043908471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219006580043908471 - 1) / 11 = 19909689094900770 from by norm_num]
      have h2 : (3 : ZMod 219006580043908471) ^ 19909689094900770 = ((59696738615302899 : ℕ) : ZMod 219006580043908471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219006580043908471 - 1) / 19 = 11526662107574130 from by norm_num]
      have h2 : (3 : ZMod 219006580043908471) ^ 11526662107574130 = ((151828471076914947 : ℕ) : ZMod 219006580043908471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219006580043908471 - 1) / 503 = 435400755554490 from by norm_num]
      have h2 : (3 : ZMod 219006580043908471) ^ 435400755554490 = ((151206675580176237 : ℕ) : ZMod 219006580043908471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6312900617).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219006580043908471 - 1) / 6312900617 = 34691910 from by norm_num]
      have h2 : (3 : ZMod 219006580043908471) ^ 34691910 = ((93255005931813887 : ℕ) : ZMod 219006580043908471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7138367505467644634573228077240753 : Nat.Prime 7138367505467644634573228077240753 := by
  refine lucas_primality 7138367505467644634573228077240753 (10 : ZMod 7138367505467644634573228077240753) ?_ (fun q hq hd => ?_)
  · rw [show 7138367505467644634573228077240753 - 1 = 7138367505467644634573228077240752 from by norm_num]
    reduce_mod_char
  · have e : 7138367505467644634573228077240753 - 1 = [2 ^ 4, 3 ^ 1, 679048043521919 ^ 1, 219006580043908471 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7138367505467644634573228077240753 - 1) / 2 = 3569183752733822317286614038620376 from by norm_num]
      have h2 : (10 : ZMod 7138367505467644634573228077240753) ^ 3569183752733822317286614038620376 = ((7138367505467644634573228077240752 : ℕ) : ZMod 7138367505467644634573228077240753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7138367505467644634573228077240753 - 1) / 3 = 2379455835155881544857742692413584 from by norm_num]
      have h2 : (10 : ZMod 7138367505467644634573228077240753) ^ 2379455835155881544857742692413584 = ((3743245481968525998396949705758233 : ℕ) : ZMod 7138367505467644634573228077240753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_679048043521919).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7138367505467644634573228077240753 - 1) / 679048043521919 = 10512315842107606608 from by norm_num]
      have h2 : (10 : ZMod 7138367505467644634573228077240753) ^ 10512315842107606608 = ((5956815691010394048673432273943401 : ℕ) : ZMod 7138367505467644634573228077240753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_219006580043908471).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7138367505467644634573228077240753 - 1) / 219006580043908471 = 32594306089052112 from by norm_num]
      have h2 : (10 : ZMod 7138367505467644634573228077240753) ^ 32594306089052112 = ((6744563549073649496439093135857493 : ℕ) : ZMod 7138367505467644634573228077240753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_385088797365931425918167320729289097437483553322960931 : Nat.Prime 385088797365931425918167320729289097437483553322960931 := by
  refine lucas_primality 385088797365931425918167320729289097437483553322960931 (2 : ZMod 385088797365931425918167320729289097437483553322960931) ?_ (fun q hq hd => ?_)
  · rw [show 385088797365931425918167320729289097437483553322960931 - 1 = 385088797365931425918167320729289097437483553322960930 from by norm_num]
    reduce_mod_char
  · have e : 385088797365931425918167320729289097437483553322960931 - 1 = [2 ^ 1, 5 ^ 1, 367 ^ 1, 1809917 ^ 1, 8121518879 ^ 1, 7138367505467644634573228077240753 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (385088797365931425918167320729289097437483553322960931 - 1) / 2 = 192544398682965712959083660364644548718741776661480465 from by norm_num]
      have h2 : (2 : ZMod 385088797365931425918167320729289097437483553322960931) ^ 192544398682965712959083660364644548718741776661480465 = ((385088797365931425918167320729289097437483553322960930 : ℕ) : ZMod 385088797365931425918167320729289097437483553322960931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (385088797365931425918167320729289097437483553322960931 - 1) / 5 = 77017759473186285183633464145857819487496710664592186 from by norm_num]
      have h2 : (2 : ZMod 385088797365931425918167320729289097437483553322960931) ^ 77017759473186285183633464145857819487496710664592186 = ((174790718234453483756414737849181479824559198152247949 : ℕ) : ZMod 385088797365931425918167320729289097437483553322960931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (385088797365931425918167320729289097437483553322960931 - 1) / 367 = 1049288276201448027024979075556646042063987883713790 from by norm_num]
      have h2 : (2 : ZMod 385088797365931425918167320729289097437483553322960931) ^ 1049288276201448027024979075556646042063987883713790 = ((18660594209333212181674887149976529284242805139162779 : ℕ) : ZMod 385088797365931425918167320729289097437483553322960931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (385088797365931425918167320729289097437483553322960931 - 1) / 1809917 = 212765998311486894657692767529830979783870505290 from by norm_num]
      have h2 : (2 : ZMod 385088797365931425918167320729289097437483553322960931) ^ 212765998311486894657692767529830979783870505290 = ((149575872162837774405189897140008395575646245316522863 : ℕ) : ZMod 385088797365931425918167320729289097437483553322960931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_8121518879).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (385088797365931425918167320729289097437483553322960931 - 1) / 8121518879 = 47415859410444082514847444797682541647328670 from by norm_num]
      have h2 : (2 : ZMod 385088797365931425918167320729289097437483553322960931) ^ 47415859410444082514847444797682541647328670 = ((349910083768728021978158608359900728820711912040987745 : ℕ) : ZMod 385088797365931425918167320729289097437483553322960931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_7138367505467644634573228077240753).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (385088797365931425918167320729289097437483553322960931 - 1) / 7138367505467644634573228077240753 = 53946339561667567810 from by norm_num]
      have h2 : (2 : ZMod 385088797365931425918167320729289097437483553322960931) ^ 53946339561667567810 = ((283548897579966384814570808757985982769713849550487620 : ℕ) : ZMod 385088797365931425918167320729289097437483553322960931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_394226184349830246792353594915553669141480163076208147970769 : Nat.Prime 394226184349830246792353594915553669141480163076208147970769 := by
  refine lucas_primality 394226184349830246792353594915553669141480163076208147970769 (3 : ZMod 394226184349830246792353594915553669141480163076208147970769) ?_ (fun q hq hd => ?_)
  · rw [show 394226184349830246792353594915553669141480163076208147970769 - 1 = 394226184349830246792353594915553669141480163076208147970768 from by norm_num]
    reduce_mod_char
  · have e : 394226184349830246792353594915553669141480163076208147970769 - 1 = [2 ^ 4, 109 ^ 1, 587 ^ 1, 385088797365931425918167320729289097437483553322960931 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (394226184349830246792353594915553669141480163076208147970769 - 1) / 2 = 197113092174915123396176797457776834570740081538104073985384 from by norm_num]
      have h2 : (3 : ZMod 394226184349830246792353594915553669141480163076208147970769) ^ 197113092174915123396176797457776834570740081538104073985384 = ((394226184349830246792353594915553669141480163076208147970768 : ℕ) : ZMod 394226184349830246792353594915553669141480163076208147970769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (394226184349830246792353594915553669141480163076208147970769 - 1) / 109 = 3616753984860827952223427476289483203132845532809249063952 from by norm_num]
      have h2 : (3 : ZMod 394226184349830246792353594915553669141480163076208147970769) ^ 3616753984860827952223427476289483203132845532809249063952 = ((201965645070362734497963023147834766198003351918944196075555 : ℕ) : ZMod 394226184349830246792353594915553669141480163076208147970769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (394226184349830246792353594915553669141480163076208147970769 - 1) / 587 = 671594862606184406801283807351880185930971316995243863664 from by norm_num]
      have h2 : (3 : ZMod 394226184349830246792353594915553669141480163076208147970769) ^ 671594862606184406801283807351880185930971316995243863664 = ((286589890820946564813813530507721308462142322438088782645143 : ℕ) : ZMod 394226184349830246792353594915553669141480163076208147970769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_385088797365931425918167320729289097437483553322960931).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (394226184349830246792353594915553669141480163076208147970769 - 1) / 385088797365931425918167320729289097437483553322960931 = 1023728 from by norm_num]
      have h2 : (3 : ZMod 394226184349830246792353594915553669141480163076208147970769) ^ 1023728 = ((355944072255408622358881229904911783346901623075976858377694 : ℕ) : ZMod 394226184349830246792353594915553669141480163076208147970769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_33714884229217 : Nat.Prime 33714884229217 := by
  refine lucas_primality 33714884229217 (5 : ZMod 33714884229217) ?_ (fun q hq hd => ?_)
  · rw [show 33714884229217 - 1 = 33714884229216 from by norm_num]
    reduce_mod_char
  · have e : 33714884229217 - 1 = [2 ^ 5, 3 ^ 1, 523 ^ 1, 15091 ^ 1, 44497 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33714884229217 - 1) / 2 = 16857442114608 from by norm_num]
      have h2 : (5 : ZMod 33714884229217) ^ 16857442114608 = ((33714884229216 : ℕ) : ZMod 33714884229217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33714884229217 - 1) / 3 = 11238294743072 from by norm_num]
      have h2 : (5 : ZMod 33714884229217) ^ 11238294743072 = ((165729888484 : ℕ) : ZMod 33714884229217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33714884229217 - 1) / 523 = 64464405792 from by norm_num]
      have h2 : (5 : ZMod 33714884229217) ^ 64464405792 = ((33186645991904 : ℕ) : ZMod 33714884229217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33714884229217 - 1) / 15091 = 2234105376 from by norm_num]
      have h2 : (5 : ZMod 33714884229217) ^ 2234105376 = ((29423843702856 : ℕ) : ZMod 33714884229217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33714884229217 - 1) / 44497 = 757688928 from by norm_num]
      have h2 : (5 : ZMod 33714884229217) ^ 757688928 = ((14982490917247 : ℕ) : ZMod 33714884229217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6773252811881236867 : Nat.Prime 6773252811881236867 := by
  refine lucas_primality 6773252811881236867 (2 : ZMod 6773252811881236867) ?_ (fun q hq hd => ?_)
  · rw [show 6773252811881236867 - 1 = 6773252811881236866 from by norm_num]
    reduce_mod_char
  · have e : 6773252811881236867 - 1 = [2 ^ 1, 3 ^ 2, 11161 ^ 1, 33714884229217 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6773252811881236867 - 1) / 2 = 3386626405940618433 from by norm_num]
      have h2 : (2 : ZMod 6773252811881236867) ^ 3386626405940618433 = ((6773252811881236866 : ℕ) : ZMod 6773252811881236867) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6773252811881236867 - 1) / 3 = 2257750937293745622 from by norm_num]
      have h2 : (2 : ZMod 6773252811881236867) ^ 2257750937293745622 = ((1769981455487817764 : ℕ) : ZMod 6773252811881236867) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6773252811881236867 - 1) / 11161 = 606867916125906 from by norm_num]
      have h2 : (2 : ZMod 6773252811881236867) ^ 606867916125906 = ((1798203310679846460 : ℕ) : ZMod 6773252811881236867) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_33714884229217).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6773252811881236867 - 1) / 33714884229217 = 200898 from by norm_num]
      have h2 : (2 : ZMod 6773252811881236867) ^ 200898 = ((5445265247667835887 : ℕ) : ZMod 6773252811881236867) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_23360190343863455255753897 : Nat.Prime 23360190343863455255753897 := by
  refine lucas_primality 23360190343863455255753897 (3 : ZMod 23360190343863455255753897) ?_ (fun q hq hd => ?_)
  · rw [show 23360190343863455255753897 - 1 = 23360190343863455255753896 from by norm_num]
    reduce_mod_char
  · have e : 23360190343863455255753897 - 1 = [2 ^ 3, 593 ^ 1, 727 ^ 1, 6773252811881236867 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23360190343863455255753897 - 1) / 2 = 11680095171931727627876948 from by norm_num]
      have h2 : (3 : ZMod 23360190343863455255753897) ^ 11680095171931727627876948 = ((23360190343863455255753896 : ℕ) : ZMod 23360190343863455255753897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23360190343863455255753897 - 1) / 593 = 39393238353901273618472 from by norm_num]
      have h2 : (3 : ZMod 23360190343863455255753897) ^ 39393238353901273618472 = ((18892713282263398374921414 : ℕ) : ZMod 23360190343863455255753897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23360190343863455255753897 - 1) / 727 = 32132311339564587697048 from by norm_num]
      have h2 : (3 : ZMod 23360190343863455255753897) ^ 32132311339564587697048 = ((10308578700729799246413486 : ℕ) : ZMod 23360190343863455255753897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6773252811881236867).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23360190343863455255753897 - 1) / 6773252811881236867 = 3448888 from by norm_num]
      have h2 : (3 : ZMod 23360190343863455255753897) ^ 3448888 = ((16927464437009621683856441 : ℕ) : ZMod 23360190343863455255753897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6391568743817 : Nat.Prime 6391568743817 := by
  refine lucas_primality 6391568743817 (3 : ZMod 6391568743817) ?_ (fun q hq hd => ?_)
  · rw [show 6391568743817 - 1 = 6391568743816 from by norm_num]
    reduce_mod_char
  · have e : 6391568743817 - 1 = [2 ^ 3, 59 ^ 1, 89 ^ 1, 367 ^ 1, 607 ^ 1, 683 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6391568743817 - 1) / 2 = 3195784371908 from by norm_num]
      have h2 : (3 : ZMod 6391568743817) ^ 3195784371908 = ((6391568743816 : ℕ) : ZMod 6391568743817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6391568743817 - 1) / 59 = 108331673624 from by norm_num]
      have h2 : (3 : ZMod 6391568743817) ^ 108331673624 = ((5979002142016 : ℕ) : ZMod 6391568743817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6391568743817 - 1) / 89 = 71815379144 from by norm_num]
      have h2 : (3 : ZMod 6391568743817) ^ 71815379144 = ((6043577307767 : ℕ) : ZMod 6391568743817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6391568743817 - 1) / 367 = 17415718648 from by norm_num]
      have h2 : (3 : ZMod 6391568743817) ^ 17415718648 = ((2902011306402 : ℕ) : ZMod 6391568743817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6391568743817 - 1) / 607 = 10529767288 from by norm_num]
      have h2 : (3 : ZMod 6391568743817) ^ 10529767288 = ((3085823836969 : ℕ) : ZMod 6391568743817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6391568743817 - 1) / 683 = 9358080152 from by norm_num]
      have h2 : (3 : ZMod 6391568743817) ^ 9358080152 = ((2433802183498 : ℕ) : ZMod 6391568743817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_326682253 : Nat.Prime 326682253 := by
  refine lucas_primality 326682253 (6 : ZMod 326682253) ?_ (fun q hq hd => ?_)
  · rw [show 326682253 - 1 = 326682252 from by norm_num]
    reduce_mod_char
  · have e : 326682253 - 1 = [2 ^ 2, 3 ^ 2, 13 ^ 1, 698039 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326682253 - 1) / 2 = 163341126 from by norm_num]
      have h2 : (6 : ZMod 326682253) ^ 163341126 = ((326682252 : ℕ) : ZMod 326682253) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326682253 - 1) / 3 = 108894084 from by norm_num]
      have h2 : (6 : ZMod 326682253) ^ 108894084 = ((110463757 : ℕ) : ZMod 326682253) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326682253 - 1) / 13 = 25129404 from by norm_num]
      have h2 : (6 : ZMod 326682253) ^ 25129404 = ((220209913 : ℕ) : ZMod 326682253) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326682253 - 1) / 698039 = 468 from by norm_num]
      have h2 : (6 : ZMod 326682253) ^ 468 = ((270113905 : ℕ) : ZMod 326682253) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2366069394177173 : Nat.Prime 2366069394177173 := by
  refine lucas_primality 2366069394177173 (3 : ZMod 2366069394177173) ?_ (fun q hq hd => ?_)
  · rw [show 2366069394177173 - 1 = 2366069394177172 from by norm_num]
    reduce_mod_char
  · have e : 2366069394177173 - 1 = [2 ^ 2, 19 ^ 1, 157 ^ 1, 607 ^ 1, 326682253 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2366069394177173 - 1) / 2 = 1183034697088586 from by norm_num]
      have h2 : (3 : ZMod 2366069394177173) ^ 1183034697088586 = ((2366069394177172 : ℕ) : ZMod 2366069394177173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2366069394177173 - 1) / 19 = 124529968114588 from by norm_num]
      have h2 : (3 : ZMod 2366069394177173) ^ 124529968114588 = ((2185460137910971 : ℕ) : ZMod 2366069394177173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2366069394177173 - 1) / 157 = 15070505695396 from by norm_num]
      have h2 : (3 : ZMod 2366069394177173) ^ 15070505695396 = ((1317112574339397 : ℕ) : ZMod 2366069394177173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2366069394177173 - 1) / 607 = 3897972642796 from by norm_num]
      have h2 : (3 : ZMod 2366069394177173) ^ 3897972642796 = ((728541392143439 : ℕ) : ZMod 2366069394177173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_326682253).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2366069394177173 - 1) / 326682253 = 7242724 from by norm_num]
      have h2 : (3 : ZMod 2366069394177173) ^ 7242724 = ((200257576144063 : ℕ) : ZMod 2366069394177173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_618590811011 : Nat.Prime 618590811011 := by
  refine lucas_primality 618590811011 (2 : ZMod 618590811011) ?_ (fun q hq hd => ?_)
  · rw [show 618590811011 - 1 = 618590811010 from by norm_num]
    reduce_mod_char
  · have e : 618590811011 - 1 = [2 ^ 1, 5 ^ 1, 881 ^ 1, 1549 ^ 1, 45329 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (618590811011 - 1) / 2 = 309295405505 from by norm_num]
      have h2 : (2 : ZMod 618590811011) ^ 309295405505 = ((618590811010 : ℕ) : ZMod 618590811011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (618590811011 - 1) / 5 = 123718162202 from by norm_num]
      have h2 : (2 : ZMod 618590811011) ^ 123718162202 = ((556826224650 : ℕ) : ZMod 618590811011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (618590811011 - 1) / 881 = 702146210 from by norm_num]
      have h2 : (2 : ZMod 618590811011) ^ 702146210 = ((289819766111 : ℕ) : ZMod 618590811011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (618590811011 - 1) / 1549 = 399348490 from by norm_num]
      have h2 : (2 : ZMod 618590811011) ^ 399348490 = ((413222195455 : ℕ) : ZMod 618590811011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (618590811011 - 1) / 45329 = 13646690 from by norm_num]
      have h2 : (2 : ZMod 618590811011) ^ 13646690 = ((132397115358 : ℕ) : ZMod 618590811011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1237181622023 : Nat.Prime 1237181622023 := by
  refine lucas_primality 1237181622023 (5 : ZMod 1237181622023) ?_ (fun q hq hd => ?_)
  · rw [show 1237181622023 - 1 = 1237181622022 from by norm_num]
    reduce_mod_char
  · have e : 1237181622023 - 1 = [2 ^ 1, 618590811011 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1237181622023 - 1) / 2 = 618590811011 from by norm_num]
      have h2 : (5 : ZMod 1237181622023) ^ 618590811011 = ((1237181622022 : ℕ) : ZMod 1237181622023) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_618590811011).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1237181622023 - 1) / 618590811011 = 2 from by norm_num]
      have h2 : (5 : ZMod 1237181622023) ^ 2 = ((25 : ℕ) : ZMod 1237181622023) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7423089732139 : Nat.Prime 7423089732139 := by
  refine lucas_primality 7423089732139 (2 : ZMod 7423089732139) ?_ (fun q hq hd => ?_)
  · rw [show 7423089732139 - 1 = 7423089732138 from by norm_num]
    reduce_mod_char
  · have e : 7423089732139 - 1 = [2 ^ 1, 3 ^ 1, 1237181622023 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7423089732139 - 1) / 2 = 3711544866069 from by norm_num]
      have h2 : (2 : ZMod 7423089732139) ^ 3711544866069 = ((7423089732138 : ℕ) : ZMod 7423089732139) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7423089732139 - 1) / 3 = 2474363244046 from by norm_num]
      have h2 : (2 : ZMod 7423089732139) ^ 2474363244046 = ((2556567796951 : ℕ) : ZMod 7423089732139) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1237181622023).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7423089732139 - 1) / 1237181622023 = 6 from by norm_num]
      have h2 : (2 : ZMod 7423089732139) ^ 6 = ((64 : ℕ) : ZMod 7423089732139) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_18201416023204829 : Nat.Prime 18201416023204829 := by
  refine lucas_primality 18201416023204829 (3 : ZMod 18201416023204829) ?_ (fun q hq hd => ?_)
  · rw [show 18201416023204829 - 1 = 18201416023204828 from by norm_num]
    reduce_mod_char
  · have e : 18201416023204829 - 1 = [2 ^ 2, 613 ^ 1, 7423089732139 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18201416023204829 - 1) / 2 = 9100708011602414 from by norm_num]
      have h2 : (3 : ZMod 18201416023204829) ^ 9100708011602414 = ((18201416023204828 : ℕ) : ZMod 18201416023204829) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18201416023204829 - 1) / 613 = 29692358928556 from by norm_num]
      have h2 : (3 : ZMod 18201416023204829) ^ 29692358928556 = ((16008671153941006 : ℕ) : ZMod 18201416023204829) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_7423089732139).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18201416023204829 - 1) / 7423089732139 = 2452 from by norm_num]
      have h2 : (3 : ZMod 18201416023204829) ^ 2452 = ((8940213428760849 : ℕ) : ZMod 18201416023204829) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_62248793 : Nat.Prime 62248793 := by
  refine lucas_primality 62248793 (3 : ZMod 62248793) ?_ (fun q hq hd => ?_)
  · rw [show 62248793 - 1 = 62248792 from by norm_num]
    reduce_mod_char
  · have e : 62248793 - 1 = [2 ^ 3, 61 ^ 1, 199 ^ 1, 641 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62248793 - 1) / 2 = 31124396 from by norm_num]
      have h2 : (3 : ZMod 62248793) ^ 31124396 = ((62248792 : ℕ) : ZMod 62248793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62248793 - 1) / 61 = 1020472 from by norm_num]
      have h2 : (3 : ZMod 62248793) ^ 1020472 = ((3635567 : ℕ) : ZMod 62248793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62248793 - 1) / 199 = 312808 from by norm_num]
      have h2 : (3 : ZMod 62248793) ^ 312808 = ((3386228 : ℕ) : ZMod 62248793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62248793 - 1) / 641 = 97112 from by norm_num]
      have h2 : (3 : ZMod 62248793) ^ 97112 = ((37773917 : ℕ) : ZMod 62248793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_104019912968999 : Nat.Prime 104019912968999 := by
  refine lucas_primality 104019912968999 (11 : ZMod 104019912968999) ?_ (fun q hq hd => ?_)
  · rw [show 104019912968999 - 1 = 104019912968998 from by norm_num]
    reduce_mod_char
  · have e : 104019912968999 - 1 = [2 ^ 1, 13 ^ 1, 802733 ^ 1, 4983931 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104019912968999 - 1) / 2 = 52009956484499 from by norm_num]
      have h2 : (11 : ZMod 104019912968999) ^ 52009956484499 = ((104019912968998 : ℕ) : ZMod 104019912968999) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104019912968999 - 1) / 13 = 8001531766846 from by norm_num]
      have h2 : (11 : ZMod 104019912968999) ^ 8001531766846 = ((49778298371593 : ℕ) : ZMod 104019912968999) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104019912968999 - 1) / 802733 = 129582206 from by norm_num]
      have h2 : (11 : ZMod 104019912968999) ^ 129582206 = ((56141134956146 : ℕ) : ZMod 104019912968999) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104019912968999 - 1) / 4983931 = 20871058 from by norm_num]
      have h2 : (11 : ZMod 104019912968999) ^ 20871058 = ((86714040042771 : ℕ) : ZMod 104019912968999) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_813428186489554222340095640950541 : Nat.Prime 813428186489554222340095640950541 := by
  refine lucas_primality 813428186489554222340095640950541 (3 : ZMod 813428186489554222340095640950541) ?_ (fun q hq hd => ?_)
  · rw [show 813428186489554222340095640950541 - 1 = 813428186489554222340095640950540 from by norm_num]
    reduce_mod_char
  · have e : 813428186489554222340095640950541 - 1 = [2 ^ 2, 5 ^ 1, 7 ^ 2, 71 ^ 2, 163 ^ 1, 641 ^ 1, 15150059 ^ 1, 104019912968999 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (813428186489554222340095640950541 - 1) / 2 = 406714093244777111170047820475270 from by norm_num]
      have h2 : (3 : ZMod 813428186489554222340095640950541) ^ 406714093244777111170047820475270 = ((813428186489554222340095640950540 : ℕ) : ZMod 813428186489554222340095640950541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (813428186489554222340095640950541 - 1) / 5 = 162685637297910844468019128190108 from by norm_num]
      have h2 : (3 : ZMod 813428186489554222340095640950541) ^ 162685637297910844468019128190108 = ((714815169180239179531245414447494 : ℕ) : ZMod 813428186489554222340095640950541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (813428186489554222340095640950541 - 1) / 7 = 116204026641364888905727948707220 from by norm_num]
      have h2 : (3 : ZMod 813428186489554222340095640950541) ^ 116204026641364888905727948707220 = ((38818163538837366324340387525905 : ℕ) : ZMod 813428186489554222340095640950541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (813428186489554222340095640950541 - 1) / 71 = 11456735020979636934367544238740 from by norm_num]
      have h2 : (3 : ZMod 813428186489554222340095640950541) ^ 11456735020979636934367544238740 = ((150363014944468106052931615098535 : ℕ) : ZMod 813428186489554222340095640950541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (813428186489554222340095640950541 - 1) / 163 = 4990356972328553511288930312580 from by norm_num]
      have h2 : (3 : ZMod 813428186489554222340095640950541) ^ 4990356972328553511288930312580 = ((721629192922318554660923807820703 : ℕ) : ZMod 813428186489554222340095640950541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (813428186489554222340095640950541 - 1) / 641 = 1268998730872939504430726428940 from by norm_num]
      have h2 : (3 : ZMod 813428186489554222340095640950541) ^ 1268998730872939504430726428940 = ((109302965371696295531878591499087 : ℕ) : ZMod 813428186489554222340095640950541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (813428186489554222340095640950541 - 1) / 15150059 = 53691420375957230420033060 from by norm_num]
      have h2 : (3 : ZMod 813428186489554222340095640950541) ^ 53691420375957230420033060 = ((561045648267026907152753336086509 : ℕ) : ZMod 813428186489554222340095640950541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_104019912968999).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (813428186489554222340095640950541 - 1) / 104019912968999 = 7819927581865789460 from by norm_num]
      have h2 : (3 : ZMod 813428186489554222340095640950541) ^ 7819927581865789460 = ((117320969893471916421145914101379 : ℕ) : ZMod 813428186489554222340095640950541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_175827017 : Nat.Prime 175827017 := by
  refine lucas_primality 175827017 (3 : ZMod 175827017) ?_ (fun q hq hd => ?_)
  · rw [show 175827017 - 1 = 175827016 from by norm_num]
    reduce_mod_char
  · have e : 175827017 - 1 = [2 ^ 3, 21978377 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175827017 - 1) / 2 = 87913508 from by norm_num]
      have h2 : (3 : ZMod 175827017) ^ 87913508 = ((175827016 : ℕ) : ZMod 175827017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175827017 - 1) / 21978377 = 8 from by norm_num]
      have h2 : (3 : ZMod 175827017) ^ 8 = ((6561 : ℕ) : ZMod 175827017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_24264128347 : Nat.Prime 24264128347 := by
  refine lucas_primality 24264128347 (2 : ZMod 24264128347) ?_ (fun q hq hd => ?_)
  · rw [show 24264128347 - 1 = 24264128346 from by norm_num]
    reduce_mod_char
  · have e : 24264128347 - 1 = [2 ^ 1, 3 ^ 1, 23 ^ 1, 175827017 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24264128347 - 1) / 2 = 12132064173 from by norm_num]
      have h2 : (2 : ZMod 24264128347) ^ 12132064173 = ((24264128346 : ℕ) : ZMod 24264128347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24264128347 - 1) / 3 = 8088042782 from by norm_num]
      have h2 : (2 : ZMod 24264128347) ^ 8088042782 = ((20764849406 : ℕ) : ZMod 24264128347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24264128347 - 1) / 23 = 1054962102 from by norm_num]
      have h2 : (2 : ZMod 24264128347) ^ 1054962102 = ((20291312202 : ℕ) : ZMod 24264128347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_175827017).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24264128347 - 1) / 175827017 = 138 from by norm_num]
      have h2 : (2 : ZMod 24264128347) ^ 138 = ((16583679669 : ℕ) : ZMod 24264128347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5926025872693688636842717229 : Nat.Prime 5926025872693688636842717229 := by
  refine lucas_primality 5926025872693688636842717229 (3 : ZMod 5926025872693688636842717229) ?_ (fun q hq hd => ?_)
  · rw [show 5926025872693688636842717229 - 1 = 5926025872693688636842717228 from by norm_num]
    reduce_mod_char
  · have e : 5926025872693688636842717229 - 1 = [2 ^ 2, 43 ^ 1, 113 ^ 1, 643 ^ 1, 8923 ^ 1, 2190131 ^ 1, 24264128347 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5926025872693688636842717229 - 1) / 2 = 2963012936346844318421358614 from by norm_num]
      have h2 : (3 : ZMod 5926025872693688636842717229) ^ 2963012936346844318421358614 = ((5926025872693688636842717228 : ℕ) : ZMod 5926025872693688636842717229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5926025872693688636842717229 - 1) / 43 = 137814555178922991554481796 from by norm_num]
      have h2 : (3 : ZMod 5926025872693688636842717229) ^ 137814555178922991554481796 = ((2174375622420092449503735886 : ℕ) : ZMod 5926025872693688636842717229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5926025872693688636842717229 - 1) / 113 = 52442706837997244573829356 from by norm_num]
      have h2 : (3 : ZMod 5926025872693688636842717229) ^ 52442706837997244573829356 = ((1916698907046807129367858585 : ℕ) : ZMod 5926025872693688636842717229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5926025872693688636842717229 - 1) / 643 = 9216214420985518875338596 from by norm_num]
      have h2 : (3 : ZMod 5926025872693688636842717229) ^ 9216214420985518875338596 = ((3470048398550246702825927395 : ℕ) : ZMod 5926025872693688636842717229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5926025872693688636842717229 - 1) / 8923 = 664129314433899880852036 from by norm_num]
      have h2 : (3 : ZMod 5926025872693688636842717229) ^ 664129314433899880852036 = ((4800232740396660194148611531 : ℕ) : ZMod 5926025872693688636842717229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5926025872693688636842717229 - 1) / 2190131 = 2705786034120191274788 from by norm_num]
      have h2 : (3 : ZMod 5926025872693688636842717229) ^ 2705786034120191274788 = ((2969376331364599479190726166 : ℕ) : ZMod 5926025872693688636842717229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_24264128347).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5926025872693688636842717229 - 1) / 24264128347 = 244229909599302724 from by norm_num]
      have h2 : (3 : ZMod 5926025872693688636842717229) ^ 244229909599302724 = ((5511471546958739285918605980 : ℕ) : ZMod 5926025872693688636842717229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3683352173 : Nat.Prime 3683352173 := by
  refine lucas_primality 3683352173 (2 : ZMod 3683352173) ?_ (fun q hq hd => ?_)
  · rw [show 3683352173 - 1 = 3683352172 from by norm_num]
    reduce_mod_char
  · have e : 3683352173 - 1 = [2 ^ 2, 31 ^ 1, 181 ^ 1, 164113 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3683352173 - 1) / 2 = 1841676086 from by norm_num]
      have h2 : (2 : ZMod 3683352173) ^ 1841676086 = ((3683352172 : ℕ) : ZMod 3683352173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3683352173 - 1) / 31 = 118817812 from by norm_num]
      have h2 : (2 : ZMod 3683352173) ^ 118817812 = ((1658613656 : ℕ) : ZMod 3683352173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3683352173 - 1) / 181 = 20350012 from by norm_num]
      have h2 : (2 : ZMod 3683352173) ^ 20350012 = ((1098822554 : ℕ) : ZMod 3683352173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3683352173 - 1) / 164113 = 22444 from by norm_num]
      have h2 : (2 : ZMod 3683352173) ^ 22444 = ((2023448593 : ℕ) : ZMod 3683352173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_416591436777528383100778409 : Nat.Prime 416591436777528383100778409 := by
  refine lucas_primality 416591436777528383100778409 (3 : ZMod 416591436777528383100778409) ?_ (fun q hq hd => ?_)
  · rw [show 416591436777528383100778409 - 1 = 416591436777528383100778408 from by norm_num]
    reduce_mod_char
  · have e : 416591436777528383100778409 - 1 = [2 ^ 3, 233 ^ 1, 283 ^ 1, 419 ^ 1, 6599 ^ 1, 77543 ^ 1, 3683352173 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (416591436777528383100778409 - 1) / 2 = 208295718388764191550389204 from by norm_num]
      have h2 : (3 : ZMod 416591436777528383100778409) ^ 208295718388764191550389204 = ((416591436777528383100778408 : ℕ) : ZMod 416591436777528383100778409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (416591436777528383100778409 - 1) / 233 = 1787946080590250571247976 from by norm_num]
      have h2 : (3 : ZMod 416591436777528383100778409) ^ 1787946080590250571247976 = ((175845371042228963444273278 : ℕ) : ZMod 416591436777528383100778409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (416591436777528383100778409 - 1) / 283 = 1472054546917061424384376 from by norm_num]
      have h2 : (3 : ZMod 416591436777528383100778409) ^ 1472054546917061424384376 = ((280898382610048472920407853 : ℕ) : ZMod 416591436777528383100778409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (416591436777528383100778409 - 1) / 419 = 994251639087179911935032 from by norm_num]
      have h2 : (3 : ZMod 416591436777528383100778409) ^ 994251639087179911935032 = ((276337627790586501020428108 : ℕ) : ZMod 416591436777528383100778409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (416591436777528383100778409 - 1) / 6599 = 63129479735949141248792 from by norm_num]
      have h2 : (3 : ZMod 416591436777528383100778409) ^ 63129479735949141248792 = ((63564316772812656167665449 : ℕ) : ZMod 416591436777528383100778409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (416591436777528383100778409 - 1) / 77543 = 5372392566415129452056 from by norm_num]
      have h2 : (3 : ZMod 416591436777528383100778409) ^ 5372392566415129452056 = ((82788396486288859890050458 : ℕ) : ZMod 416591436777528383100778409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3683352173).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (416591436777528383100778409 - 1) / 3683352173 = 113101169046842696 from by norm_num]
      have h2 : (3 : ZMod 416591436777528383100778409) ^ 113101169046842696 = ((8135924969546769789585198 : ℕ) : ZMod 416591436777528383100778409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6608806553038710269510748680377 : Nat.Prime 6608806553038710269510748680377 := by
  refine lucas_primality 6608806553038710269510748680377 (5 : ZMod 6608806553038710269510748680377) ?_ (fun q hq hd => ?_)
  · rw [show 6608806553038710269510748680377 - 1 = 6608806553038710269510748680376 from by norm_num]
    reduce_mod_char
  · have e : 6608806553038710269510748680377 - 1 = [2 ^ 3, 3 ^ 1, 661 ^ 1, 416591436777528383100778409 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6608806553038710269510748680377 - 1) / 2 = 3304403276519355134755374340188 from by norm_num]
      have h2 : (5 : ZMod 6608806553038710269510748680377) ^ 3304403276519355134755374340188 = ((6608806553038710269510748680376 : ℕ) : ZMod 6608806553038710269510748680377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6608806553038710269510748680377 - 1) / 3 = 2202935517679570089836916226792 from by norm_num]
      have h2 : (5 : ZMod 6608806553038710269510748680377) ^ 2202935517679570089836916226792 = ((3504444576996997864758456487230 : ℕ) : ZMod 6608806553038710269510748680377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6608806553038710269510748680377 - 1) / 661 = 9998194482660681194418681816 from by norm_num]
      have h2 : (5 : ZMod 6608806553038710269510748680377) ^ 9998194482660681194418681816 = ((2627765047792510159857791508494 : ℕ) : ZMod 6608806553038710269510748680377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_416591436777528383100778409).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6608806553038710269510748680377 - 1) / 416591436777528383100778409 = 15864 from by norm_num]
      have h2 : (5 : ZMod 6608806553038710269510748680377) ^ 15864 = ((5971579681471233187020780801484 : ℕ) : ZMod 6608806553038710269510748680377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_158387833 : Nat.Prime 158387833 := by
  refine lucas_primality 158387833 (5 : ZMod 158387833) ?_ (fun q hq hd => ?_)
  · rw [show 158387833 - 1 = 158387832 from by norm_num]
    reduce_mod_char
  · have e : 158387833 - 1 = [2 ^ 3, 3 ^ 3, 733277 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (158387833 - 1) / 2 = 79193916 from by norm_num]
      have h2 : (5 : ZMod 158387833) ^ 79193916 = ((158387832 : ℕ) : ZMod 158387833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (158387833 - 1) / 3 = 52795944 from by norm_num]
      have h2 : (5 : ZMod 158387833) ^ 52795944 = ((42657647 : ℕ) : ZMod 158387833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (158387833 - 1) / 733277 = 216 from by norm_num]
      have h2 : (5 : ZMod 158387833) ^ 216 = ((108893953 : ℕ) : ZMod 158387833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_19956866959 : Nat.Prime 19956866959 := by
  refine lucas_primality 19956866959 (6 : ZMod 19956866959) ?_ (fun q hq hd => ?_)
  · rw [show 19956866959 - 1 = 19956866958 from by norm_num]
    reduce_mod_char
  · have e : 19956866959 - 1 = [2 ^ 1, 3 ^ 2, 7 ^ 1, 158387833 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19956866959 - 1) / 2 = 9978433479 from by norm_num]
      have h2 : (6 : ZMod 19956866959) ^ 9978433479 = ((19956866958 : ℕ) : ZMod 19956866959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19956866959 - 1) / 3 = 6652288986 from by norm_num]
      have h2 : (6 : ZMod 19956866959) ^ 6652288986 = ((18839346748 : ℕ) : ZMod 19956866959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19956866959 - 1) / 7 = 2850980994 from by norm_num]
      have h2 : (6 : ZMod 19956866959) ^ 2850980994 = ((13198861792 : ℕ) : ZMod 19956866959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_158387833).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19956866959 - 1) / 158387833 = 126 from by norm_num]
      have h2 : (6 : ZMod 19956866959) ^ 126 = ((5200081337 : ℕ) : ZMod 19956866959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_214702722041899636147 : Nat.Prime 214702722041899636147 := by
  refine lucas_primality 214702722041899636147 (3 : ZMod 214702722041899636147) ?_ (fun q hq hd => ?_)
  · rw [show 214702722041899636147 - 1 = 214702722041899636146 from by norm_num]
    reduce_mod_char
  · have e : 214702722041899636147 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 97 ^ 1, 1129 ^ 1, 2339 ^ 1, 19956866959 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (214702722041899636147 - 1) / 2 = 107351361020949818073 from by norm_num]
      have h2 : (3 : ZMod 214702722041899636147) ^ 107351361020949818073 = ((214702722041899636146 : ℕ) : ZMod 214702722041899636147) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (214702722041899636147 - 1) / 3 = 71567574013966545382 from by norm_num]
      have h2 : (3 : ZMod 214702722041899636147) ^ 71567574013966545382 = ((151692559887070480382 : ℕ) : ZMod 214702722041899636147) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (214702722041899636147 - 1) / 7 = 30671817434557090878 from by norm_num]
      have h2 : (3 : ZMod 214702722041899636147) ^ 30671817434557090878 = ((156700352944524733276 : ℕ) : ZMod 214702722041899636147) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (214702722041899636147 - 1) / 97 = 2213430124143295218 from by norm_num]
      have h2 : (3 : ZMod 214702722041899636147) ^ 2213430124143295218 = ((52412382507992725315 : ℕ) : ZMod 214702722041899636147) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (214702722041899636147 - 1) / 1129 = 190170701542869474 from by norm_num]
      have h2 : (3 : ZMod 214702722041899636147) ^ 190170701542869474 = ((161858187151435144309 : ℕ) : ZMod 214702722041899636147) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (214702722041899636147 - 1) / 2339 = 91792527593800614 from by norm_num]
      have h2 : (3 : ZMod 214702722041899636147) ^ 91792527593800614 = ((106955455584507082331 : ℕ) : ZMod 214702722041899636147) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_19956866959).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (214702722041899636147 - 1) / 19956866959 = 10758338094 from by norm_num]
      have h2 : (3 : ZMod 214702722041899636147) ^ 10758338094 = ((131032691837813388882 : ℕ) : ZMod 214702722041899636147) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_16563559810268221894218464389381741 : Nat.Prime 16563559810268221894218464389381741 := by
  refine lucas_primality 16563559810268221894218464389381741 (2 : ZMod 16563559810268221894218464389381741) ?_ (fun q hq hd => ?_)
  · rw [show 16563559810268221894218464389381741 - 1 = 16563559810268221894218464389381740 from by norm_num]
    reduce_mod_char
  · have e : 16563559810268221894218464389381741 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 17 ^ 1, 691 ^ 1, 2621 ^ 1, 41761 ^ 1, 214702722041899636147 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16563559810268221894218464389381741 - 1) / 2 = 8281779905134110947109232194690870 from by norm_num]
      have h2 : (2 : ZMod 16563559810268221894218464389381741) ^ 8281779905134110947109232194690870 = ((16563559810268221894218464389381740 : ℕ) : ZMod 16563559810268221894218464389381741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16563559810268221894218464389381741 - 1) / 3 = 5521186603422740631406154796460580 from by norm_num]
      have h2 : (2 : ZMod 16563559810268221894218464389381741) ^ 5521186603422740631406154796460580 = ((7507517069086216099036278360052838 : ℕ) : ZMod 16563559810268221894218464389381741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16563559810268221894218464389381741 - 1) / 5 = 3312711962053644378843692877876348 from by norm_num]
      have h2 : (2 : ZMod 16563559810268221894218464389381741) ^ 3312711962053644378843692877876348 = ((10893113636891285745497165878596074 : ℕ) : ZMod 16563559810268221894218464389381741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16563559810268221894218464389381741 - 1) / 17 = 974327047662836582012850846434220 from by norm_num]
      have h2 : (2 : ZMod 16563559810268221894218464389381741) ^ 974327047662836582012850846434220 = ((2365968042673416094878145710628757 : ℕ) : ZMod 16563559810268221894218464389381741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16563559810268221894218464389381741 - 1) / 691 = 23970419407045183638521656135140 from by norm_num]
      have h2 : (2 : ZMod 16563559810268221894218464389381741) ^ 23970419407045183638521656135140 = ((15141704064028876561440630501696816 : ℕ) : ZMod 16563559810268221894218464389381741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16563559810268221894218464389381741 - 1) / 2621 = 6319557348442663828393156958940 from by norm_num]
      have h2 : (2 : ZMod 16563559810268221894218464389381741) ^ 6319557348442663828393156958940 = ((3838797276282913808337601816575289 : ℕ) : ZMod 16563559810268221894218464389381741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16563559810268221894218464389381741 - 1) / 41761 = 396627470852427429760265903340 from by norm_num]
      have h2 : (2 : ZMod 16563559810268221894218464389381741) ^ 396627470852427429760265903340 = ((618608376038928106199743084540057 : ℕ) : ZMod 16563559810268221894218464389381741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_214702722041899636147).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16563559810268221894218464389381741 - 1) / 214702722041899636147 = 77146482600420 from by norm_num]
      have h2 : (2 : ZMod 16563559810268221894218464389381741) ^ 77146482600420 = ((661585552916467826410115233224404 : ℕ) : ZMod 16563559810268221894218464389381741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2032650571368784707170401 : Nat.Prime 2032650571368784707170401 := by
  refine lucas_primality 2032650571368784707170401 (33 : ZMod 2032650571368784707170401) ?_ (fun q hq hd => ?_)
  · rw [show 2032650571368784707170401 - 1 = 2032650571368784707170400 from by norm_num]
    reduce_mod_char
  · have e : 2032650571368784707170401 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 2, 1667 ^ 1, 39451 ^ 1, 766891 ^ 1, 16792843 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2032650571368784707170401 - 1) / 2 = 1016325285684392353585200 from by norm_num]
      have h2 : (33 : ZMod 2032650571368784707170401) ^ 1016325285684392353585200 = ((2032650571368784707170400 : ℕ) : ZMod 2032650571368784707170401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2032650571368784707170401 - 1) / 3 = 677550190456261569056800 from by norm_num]
      have h2 : (33 : ZMod 2032650571368784707170401) ^ 677550190456261569056800 = ((1274920913622901508291281 : ℕ) : ZMod 2032650571368784707170401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2032650571368784707170401 - 1) / 5 = 406530114273756941434080 from by norm_num]
      have h2 : (33 : ZMod 2032650571368784707170401) ^ 406530114273756941434080 = ((1530311537633737729500324 : ℕ) : ZMod 2032650571368784707170401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2032650571368784707170401 - 1) / 1667 = 1219346473526565511200 from by norm_num]
      have h2 : (33 : ZMod 2032650571368784707170401) ^ 1219346473526565511200 = ((222214919867652963462230 : ℕ) : ZMod 2032650571368784707170401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2032650571368784707170401 - 1) / 39451 = 51523423268580890400 from by norm_num]
      have h2 : (33 : ZMod 2032650571368784707170401) ^ 51523423268580890400 = ((1034366604061553755222120 : ℕ) : ZMod 2032650571368784707170401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2032650571368784707170401 - 1) / 766891 = 2650507792331354400 from by norm_num]
      have h2 : (33 : ZMod 2032650571368784707170401) ^ 2650507792331354400 = ((1530273946869548290936686 : ℕ) : ZMod 2032650571368784707170401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2032650571368784707170401 - 1) / 16792843 = 121042671057472800 from by norm_num]
      have h2 : (33 : ZMod 2032650571368784707170401) ^ 121042671057472800 = ((1530616465510263981222834 : ℕ) : ZMod 2032650571368784707170401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_109395941 : Nat.Prime 109395941 := by
  refine lucas_primality 109395941 (2 : ZMod 109395941) ?_ (fun q hq hd => ?_)
  · rw [show 109395941 - 1 = 109395940 from by norm_num]
    reduce_mod_char
  · have e : 109395941 - 1 = [2 ^ 2, 5 ^ 1, 569 ^ 1, 9613 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109395941 - 1) / 2 = 54697970 from by norm_num]
      have h2 : (2 : ZMod 109395941) ^ 54697970 = ((109395940 : ℕ) : ZMod 109395941) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109395941 - 1) / 5 = 21879188 from by norm_num]
      have h2 : (2 : ZMod 109395941) ^ 21879188 = ((98135649 : ℕ) : ZMod 109395941) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109395941 - 1) / 569 = 192260 from by norm_num]
      have h2 : (2 : ZMod 109395941) ^ 192260 = ((98895753 : ℕ) : ZMod 109395941) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109395941 - 1) / 9613 = 11380 from by norm_num]
      have h2 : (2 : ZMod 109395941) ^ 11380 = ((1891067 : ℕ) : ZMod 109395941) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_77323353608284863403150817040930314294291149972109317262405018115863298721488023177 : Nat.Prime 77323353608284863403150817040930314294291149972109317262405018115863298721488023177 := by
  refine lucas_primality 77323353608284863403150817040930314294291149972109317262405018115863298721488023177 (3 : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) ?_ (fun q hq hd => ?_)
  · rw [show 77323353608284863403150817040930314294291149972109317262405018115863298721488023177 - 1 = 77323353608284863403150817040930314294291149972109317262405018115863298721488023176 from by norm_num]
    reduce_mod_char
  · have e : 77323353608284863403150817040930314294291149972109317262405018115863298721488023177 - 1 = [2 ^ 3, 19 ^ 1, 691 ^ 1, 23447 ^ 1, 8524799 ^ 1, 109395941 ^ 1, 2032650571368784707170401 ^ 1, 16563559810268221894218464389381741 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77323353608284863403150817040930314294291149972109317262405018115863298721488023177 - 1) / 2 = 38661676804142431701575408520465157147145574986054658631202509057931649360744011588 from by norm_num]
      have h2 : (3 : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) ^ 38661676804142431701575408520465157147145574986054658631202509057931649360744011588 = ((77323353608284863403150817040930314294291149972109317262405018115863298721488023176 : ℕ) : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77323353608284863403150817040930314294291149972109317262405018115863298721488023177 - 1) / 19 = 4069650189909729652797411423206858647067955261689964066442369374519120985341474904 from by norm_num]
      have h2 : (3 : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) ^ 4069650189909729652797411423206858647067955261689964066442369374519120985341474904 = ((72052840179579070264502912399989407031351068535236208108597143057153968281385741246 : ℕ) : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77323353608284863403150817040930314294291149972109317262405018115863298721488023177 - 1) / 691 = 111900656451931784953908563011476576402736830639810878816794526940467870798101336 from by norm_num]
      have h2 : (3 : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) ^ 111900656451931784953908563011476576402736830639810878816794526940467870798101336 = ((71303762581712770559684712384190595927671579552697580050166070475406892734387219914 : ℕ) : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77323353608284863403150817040930314294291149972109317262405018115863298721488023177 - 1) / 23447 = 3297793048504493683761283620119005173126248559393923199659018983915353722074808 from by norm_num]
      have h2 : (3 : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) ^ 3297793048504493683761283620119005173126248559393923199659018983915353722074808 = ((17632414034129812299625214084453332208630122002880978577390154651424845280766699945 : ℕ) : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77323353608284863403150817040930314294291149972109317262405018115863298721488023177 - 1) / 8524799 = 9070401965874487293266482534184127308373036123445176509429139398578582172024 from by norm_num]
      have h2 : (3 : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) ^ 9070401965874487293266482534184127308373036123445176509429139398578582172024 = ((11455235523336846687837701002832088882762627342671449938472302298154699165743356473 : ℕ) : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_109395941).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77323353608284863403150817040930314294291149972109317262405018115863298721488023177 - 1) / 109395941 = 706821047485526573633575829298184969168930591054647240178728551874363407336 from by norm_num]
      have h2 : (3 : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) ^ 706821047485526573633575829298184969168930591054647240178728551874363407336 = ((74990657460541663973975056148504752516754045352056357927296730818037313735156113444 : ℕ) : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2032650571368784707170401).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77323353608284863403150817040930314294291149972109317262405018115863298721488023177 - 1) / 2032650571368784707170401 = 38040652287921479932803782059592762014835593415141286992776 from by norm_num]
      have h2 : (3 : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) ^ 38040652287921479932803782059592762014835593415141286992776 = ((43230655998833161684223161134549801312022041119030353167040643061579239673022326013 : ℕ) : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_16563559810268221894218464389381741).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77323353608284863403150817040930314294291149972109317262405018115863298721488023177 - 1) / 16563559810268221894218464389381741 = 4668281123985794222656961885309915283304282010536 from by norm_num]
      have h2 : (3 : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) ^ 4668281123985794222656961885309915283304282010536 = ((21328681930167379814295607914245759372375175802272118427038309095919743559047638307 : ℕ) : ZMod 77323353608284863403150817040930314294291149972109317262405018115863298721488023177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4846812462461 : Nat.Prime 4846812462461 := by
  refine lucas_primality 4846812462461 (3 : ZMod 4846812462461) ?_ (fun q hq hd => ?_)
  · rw [show 4846812462461 - 1 = 4846812462460 from by norm_num]
    reduce_mod_char
  · have e : 4846812462461 - 1 = [2 ^ 2, 5 ^ 1, 71 ^ 1, 389 ^ 1, 701 ^ 1, 12517 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4846812462461 - 1) / 2 = 2423406231230 from by norm_num]
      have h2 : (3 : ZMod 4846812462461) ^ 2423406231230 = ((4846812462460 : ℕ) : ZMod 4846812462461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4846812462461 - 1) / 5 = 969362492492 from by norm_num]
      have h2 : (3 : ZMod 4846812462461) ^ 969362492492 = ((244572872329 : ℕ) : ZMod 4846812462461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4846812462461 - 1) / 71 = 68264964260 from by norm_num]
      have h2 : (3 : ZMod 4846812462461) ^ 68264964260 = ((1830619825499 : ℕ) : ZMod 4846812462461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4846812462461 - 1) / 389 = 12459672140 from by norm_num]
      have h2 : (3 : ZMod 4846812462461) ^ 12459672140 = ((1313961398387 : ℕ) : ZMod 4846812462461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4846812462461 - 1) / 701 = 6914140460 from by norm_num]
      have h2 : (3 : ZMod 4846812462461) ^ 6914140460 = ((2179424321198 : ℕ) : ZMod 4846812462461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4846812462461 - 1) / 12517 = 387218380 from by norm_num]
      have h2 : (3 : ZMod 4846812462461) ^ 387218380 = ((4368161529287 : ℕ) : ZMod 4846812462461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_14120507197 : Nat.Prime 14120507197 := by
  refine lucas_primality 14120507197 (5 : ZMod 14120507197) ?_ (fun q hq hd => ?_)
  · rw [show 14120507197 - 1 = 14120507196 from by norm_num]
    reduce_mod_char
  · have e : 14120507197 - 1 = [2 ^ 2, 3 ^ 3, 7481 ^ 1, 17477 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14120507197 - 1) / 2 = 7060253598 from by norm_num]
      have h2 : (5 : ZMod 14120507197) ^ 7060253598 = ((14120507196 : ℕ) : ZMod 14120507197) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14120507197 - 1) / 3 = 4706835732 from by norm_num]
      have h2 : (5 : ZMod 14120507197) ^ 4706835732 = ((6585661885 : ℕ) : ZMod 14120507197) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14120507197 - 1) / 7481 = 1887516 from by norm_num]
      have h2 : (5 : ZMod 14120507197) ^ 1887516 = ((11784649976 : ℕ) : ZMod 14120507197) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14120507197 - 1) / 17477 = 807948 from by norm_num]
      have h2 : (5 : ZMod 14120507197) ^ 807948 = ((9572050084 : ℕ) : ZMod 14120507197) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_258414629651 : Nat.Prime 258414629651 := by
  refine lucas_primality 258414629651 (2 : ZMod 258414629651) ?_ (fun q hq hd => ?_)
  · rw [show 258414629651 - 1 = 258414629650 from by norm_num]
    reduce_mod_char
  · have e : 258414629651 - 1 = [2 ^ 1, 5 ^ 2, 43 ^ 1, 1087 ^ 1, 110573 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (258414629651 - 1) / 2 = 129207314825 from by norm_num]
      have h2 : (2 : ZMod 258414629651) ^ 129207314825 = ((258414629650 : ℕ) : ZMod 258414629651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (258414629651 - 1) / 5 = 51682925930 from by norm_num]
      have h2 : (2 : ZMod 258414629651) ^ 51682925930 = ((208231691419 : ℕ) : ZMod 258414629651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (258414629651 - 1) / 43 = 6009642550 from by norm_num]
      have h2 : (2 : ZMod 258414629651) ^ 6009642550 = ((149821839218 : ℕ) : ZMod 258414629651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (258414629651 - 1) / 1087 = 237731950 from by norm_num]
      have h2 : (2 : ZMod 258414629651) ^ 237731950 = ((130161224623 : ℕ) : ZMod 258414629651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (258414629651 - 1) / 110573 = 2337050 from by norm_num]
      have h2 : (2 : ZMod 258414629651) ^ 2337050 = ((239326541645 : ℕ) : ZMod 258414629651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_401111704973541503 : Nat.Prime 401111704973541503 := by
  refine lucas_primality 401111704973541503 (5 : ZMod 401111704973541503) ?_ (fun q hq hd => ?_)
  · rw [show 401111704973541503 - 1 = 401111704973541502 from by norm_num]
    reduce_mod_char
  · have e : 401111704973541503 - 1 = [2 ^ 1, 17 ^ 1, 71 ^ 1, 643 ^ 1, 258414629651 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (401111704973541503 - 1) / 2 = 200555852486770751 from by norm_num]
      have h2 : (5 : ZMod 401111704973541503) ^ 200555852486770751 = ((401111704973541502 : ℕ) : ZMod 401111704973541503) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (401111704973541503 - 1) / 17 = 23594806174914206 from by norm_num]
      have h2 : (5 : ZMod 401111704973541503) ^ 23594806174914206 = ((167861747011499596 : ℕ) : ZMod 401111704973541503) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (401111704973541503 - 1) / 71 = 5649460633430162 from by norm_num]
      have h2 : (5 : ZMod 401111704973541503) ^ 5649460633430162 = ((144512020902827956 : ℕ) : ZMod 401111704973541503) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (401111704973541503 - 1) / 643 = 623812915977514 from by norm_num]
      have h2 : (5 : ZMod 401111704973541503) ^ 623812915977514 = ((203964706167515868 : ℕ) : ZMod 401111704973541503) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_258414629651).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (401111704973541503 - 1) / 258414629651 = 1552202 from by norm_num]
      have h2 : (5 : ZMod 401111704973541503) ^ 1552202 = ((275319111079691976 : ℕ) : ZMod 401111704973541503) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6208351993 : Nat.Prime 6208351993 := by
  refine lucas_primality 6208351993 (11 : ZMod 6208351993) ?_ (fun q hq hd => ?_)
  · rw [show 6208351993 - 1 = 6208351992 from by norm_num]
    reduce_mod_char
  · have e : 6208351993 - 1 = [2 ^ 3, 3 ^ 2, 17 ^ 1, 19 ^ 1, 266957 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6208351993 - 1) / 2 = 3104175996 from by norm_num]
      have h2 : (11 : ZMod 6208351993) ^ 3104175996 = ((6208351992 : ℕ) : ZMod 6208351993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6208351993 - 1) / 3 = 2069450664 from by norm_num]
      have h2 : (11 : ZMod 6208351993) ^ 2069450664 = ((5521418701 : ℕ) : ZMod 6208351993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6208351993 - 1) / 17 = 365197176 from by norm_num]
      have h2 : (11 : ZMod 6208351993) ^ 365197176 = ((2675791309 : ℕ) : ZMod 6208351993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6208351993 - 1) / 19 = 326755368 from by norm_num]
      have h2 : (11 : ZMod 6208351993) ^ 326755368 = ((476636581 : ℕ) : ZMod 6208351993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6208351993 - 1) / 266957 = 23256 from by norm_num]
      have h2 : (11 : ZMod 6208351993) ^ 23256 = ((806968244 : ℕ) : ZMod 6208351993) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_372501119581 : Nat.Prime 372501119581 := by
  refine lucas_primality 372501119581 (2 : ZMod 372501119581) ?_ (fun q hq hd => ?_)
  · rw [show 372501119581 - 1 = 372501119580 from by norm_num]
    reduce_mod_char
  · have e : 372501119581 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 6208351993 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (372501119581 - 1) / 2 = 186250559790 from by norm_num]
      have h2 : (2 : ZMod 372501119581) ^ 186250559790 = ((372501119580 : ℕ) : ZMod 372501119581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (372501119581 - 1) / 3 = 124167039860 from by norm_num]
      have h2 : (2 : ZMod 372501119581) ^ 124167039860 = ((212262897864 : ℕ) : ZMod 372501119581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (372501119581 - 1) / 5 = 74500223916 from by norm_num]
      have h2 : (2 : ZMod 372501119581) ^ 74500223916 = ((83844796584 : ℕ) : ZMod 372501119581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6208351993).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (372501119581 - 1) / 6208351993 = 60 from by norm_num]
      have h2 : (2 : ZMod 372501119581) ^ 60 = ((366912965915 : ℕ) : ZMod 372501119581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15434303023994570927 : Nat.Prime 15434303023994570927 := by
  refine lucas_primality 15434303023994570927 (5 : ZMod 15434303023994570927) ?_ (fun q hq hd => ?_)
  · rw [show 15434303023994570927 - 1 = 15434303023994570926 from by norm_num]
    reduce_mod_char
  · have e : 15434303023994570927 - 1 = [2 ^ 1, 7 ^ 1, 2959589 ^ 1, 372501119581 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15434303023994570927 - 1) / 2 = 7717151511997285463 from by norm_num]
      have h2 : (5 : ZMod 15434303023994570927) ^ 7717151511997285463 = ((15434303023994570926 : ℕ) : ZMod 15434303023994570927) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15434303023994570927 - 1) / 7 = 2204900431999224418 from by norm_num]
      have h2 : (5 : ZMod 15434303023994570927) ^ 2204900431999224418 = ((6354370511935970814 : ℕ) : ZMod 15434303023994570927) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15434303023994570927 - 1) / 2959589 = 5215015674134 from by norm_num]
      have h2 : (5 : ZMod 15434303023994570927) ^ 5215015674134 = ((13632989210818988560 : ℕ) : ZMod 15434303023994570927) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_372501119581).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15434303023994570927 - 1) / 372501119581 = 41434246 from by norm_num]
      have h2 : (5 : ZMod 15434303023994570927) ^ 41434246 = ((1069171158850772711 : ℕ) : ZMod 15434303023994570927) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_16494815758321902827664653884456105022034001119493371936617 : Nat.Prime 16494815758321902827664653884456105022034001119493371936617 := by
  refine lucas_primality 16494815758321902827664653884456105022034001119493371936617 (3 : ZMod 16494815758321902827664653884456105022034001119493371936617) ?_ (fun q hq hd => ?_)
  · rw [show 16494815758321902827664653884456105022034001119493371936617 - 1 = 16494815758321902827664653884456105022034001119493371936616 from by norm_num]
    reduce_mod_char
  · have e : 16494815758321902827664653884456105022034001119493371936617 - 1 = [2 ^ 3, 11 ^ 1, 67 ^ 1, 71 ^ 1, 643 ^ 1, 701 ^ 1, 14120507197 ^ 1, 401111704973541503 ^ 1, 15434303023994570927 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16494815758321902827664653884456105022034001119493371936617 - 1) / 2 = 8247407879160951413832326942228052511017000559746685968308 from by norm_num]
      have h2 : (3 : ZMod 16494815758321902827664653884456105022034001119493371936617) ^ 8247407879160951413832326942228052511017000559746685968308 = ((16494815758321902827664653884456105022034001119493371936616 : ℕ) : ZMod 16494815758321902827664653884456105022034001119493371936617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16494815758321902827664653884456105022034001119493371936617 - 1) / 11 = 1499528705301991166151332171314191365639454647226670176056 from by norm_num]
      have h2 : (3 : ZMod 16494815758321902827664653884456105022034001119493371936617) ^ 1499528705301991166151332171314191365639454647226670176056 = ((3688881266493808175793066947429200142714721631623149068820 : ℕ) : ZMod 16494815758321902827664653884456105022034001119493371936617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16494815758321902827664653884456105022034001119493371936617 - 1) / 67 = 246191279974953773547233640066509030179611957007363760248 from by norm_num]
      have h2 : (3 : ZMod 16494815758321902827664653884456105022034001119493371936617) ^ 246191279974953773547233640066509030179611957007363760248 = ((1440634246257137373967373529185757102000526308292527625562 : ℕ) : ZMod 16494815758321902827664653884456105022034001119493371936617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16494815758321902827664653884456105022034001119493371936617 - 1) / 71 = 232321348708759194755840195555719789042732410133709463896 from by norm_num]
      have h2 : (3 : ZMod 16494815758321902827664653884456105022034001119493371936617) ^ 232321348708759194755840195555719789042732410133709463896 = ((14275098035187565297574730737701849577805784120638643949744 : ℕ) : ZMod 16494815758321902827664653884456105022034001119493371936617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16494815758321902827664653884456105022034001119493371936617 - 1) / 643 = 25652901645912757119229632790755995368637637821918152312 from by norm_num]
      have h2 : (3 : ZMod 16494815758321902827664653884456105022034001119493371936617) ^ 25652901645912757119229632790755995368637637821918152312 = ((8664888212185961718037443515932358295750526612486608975282 : ℕ) : ZMod 16494815758321902827664653884456105022034001119493371936617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16494815758321902827664653884456105022034001119493371936617 - 1) / 701 = 23530407643825824290534456325900292470804566504270145416 from by norm_num]
      have h2 : (3 : ZMod 16494815758321902827664653884456105022034001119493371936617) ^ 23530407643825824290534456325900292470804566504270145416 = ((16494815758321902827664653884456105022033983105094862454633 : ℕ) : ZMod 16494815758321902827664653884456105022034001119493371936617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_14120507197).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16494815758321902827664653884456105022034001119493371936617 - 1) / 14120507197 = 1168146124512180497397515251906011618177004008328 from by norm_num]
      have h2 : (3 : ZMod 16494815758321902827664653884456105022034001119493371936617) ^ 1168146124512180497397515251906011618177004008328 = ((2040945396268794739609753228572472754116214996344629941453 : ℕ) : ZMod 16494815758321902827664653884456105022034001119493371936617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_401111704973541503).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16494815758321902827664653884456105022034001119493371936617 - 1) / 401111704973541503 = 41122748485761463742642284935580263582872 from by norm_num]
      have h2 : (3 : ZMod 16494815758321902827664653884456105022034001119493371936617) ^ 41122748485761463742642284935580263582872 = ((15261453209107762421718483357882316501308466891556694937665 : ℕ) : ZMod 16494815758321902827664653884456105022034001119493371936617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_15434303023994570927).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16494815758321902827664653884456105022034001119493371936617 - 1) / 15434303023994570927 = 1068711410724451313580054660557147619608 from by norm_num]
      have h2 : (3 : ZMod 16494815758321902827664653884456105022034001119493371936617) ^ 1068711410724451313580054660557147619608 = ((5057907752386351011025174259632591962393810104228003367847 : ℕ) : ZMod 16494815758321902827664653884456105022034001119493371936617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_238439401 : Nat.Prime 238439401 := by
  refine lucas_primality 238439401 (11 : ZMod 238439401) ?_ (fun q hq hd => ?_)
  · rw [show 238439401 - 1 = 238439400 from by norm_num]
    reduce_mod_char
  · have e : 238439401 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 2, 587 ^ 1, 677 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (238439401 - 1) / 2 = 119219700 from by norm_num]
      have h2 : (11 : ZMod 238439401) ^ 119219700 = ((238439400 : ℕ) : ZMod 238439401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (238439401 - 1) / 3 = 79479800 from by norm_num]
      have h2 : (11 : ZMod 238439401) ^ 79479800 = ((207693081 : ℕ) : ZMod 238439401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (238439401 - 1) / 5 = 47687880 from by norm_num]
      have h2 : (11 : ZMod 238439401) ^ 47687880 = ((229164578 : ℕ) : ZMod 238439401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (238439401 - 1) / 587 = 406200 from by norm_num]
      have h2 : (11 : ZMod 238439401) ^ 406200 = ((101933656 : ℕ) : ZMod 238439401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (238439401 - 1) / 677 = 352200 from by norm_num]
      have h2 : (11 : ZMod 238439401) ^ 352200 = ((65038823 : ℕ) : ZMod 238439401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_447312316277 : Nat.Prime 447312316277 := by
  refine lucas_primality 447312316277 (2 : ZMod 447312316277) ?_ (fun q hq hd => ?_)
  · rw [show 447312316277 - 1 = 447312316276 from by norm_num]
    reduce_mod_char
  · have e : 447312316277 - 1 = [2 ^ 2, 7 ^ 1, 67 ^ 1, 238439401 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (447312316277 - 1) / 2 = 223656158138 from by norm_num]
      have h2 : (2 : ZMod 447312316277) ^ 223656158138 = ((447312316276 : ℕ) : ZMod 447312316277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (447312316277 - 1) / 7 = 63901759468 from by norm_num]
      have h2 : (2 : ZMod 447312316277) ^ 63901759468 = ((253575185341 : ℕ) : ZMod 447312316277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (447312316277 - 1) / 67 = 6676303228 from by norm_num]
      have h2 : (2 : ZMod 447312316277) ^ 6676303228 = ((264834850682 : ℕ) : ZMod 447312316277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_238439401).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (447312316277 - 1) / 238439401 = 1876 from by norm_num]
      have h2 : (2 : ZMod 447312316277) ^ 1876 = ((274313655909 : ℕ) : ZMod 447312316277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_42040200732977569 : Nat.Prime 42040200732977569 := by
  refine lucas_primality 42040200732977569 (7 : ZMod 42040200732977569) ?_ (fun q hq hd => ?_)
  · rw [show 42040200732977569 - 1 = 42040200732977568 from by norm_num]
    reduce_mod_char
  · have e : 42040200732977569 - 1 = [2 ^ 5, 3 ^ 1, 11 ^ 1, 89 ^ 1, 447312316277 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42040200732977569 - 1) / 2 = 21020100366488784 from by norm_num]
      have h2 : (7 : ZMod 42040200732977569) ^ 21020100366488784 = ((42040200732977568 : ℕ) : ZMod 42040200732977569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42040200732977569 - 1) / 3 = 14013400244325856 from by norm_num]
      have h2 : (7 : ZMod 42040200732977569) ^ 14013400244325856 = ((17650139996752921 : ℕ) : ZMod 42040200732977569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42040200732977569 - 1) / 11 = 3821836430270688 from by norm_num]
      have h2 : (7 : ZMod 42040200732977569) ^ 3821836430270688 = ((2590722598801174 : ℕ) : ZMod 42040200732977569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42040200732977569 - 1) / 89 = 472361805988512 from by norm_num]
      have h2 : (7 : ZMod 42040200732977569) ^ 472361805988512 = ((24619805293884022 : ℕ) : ZMod 42040200732977569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_447312316277).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42040200732977569 - 1) / 447312316277 = 93984 from by norm_num]
      have h2 : (7 : ZMod 42040200732977569) ^ 93984 = ((30492807081262081 : ℕ) : ZMod 42040200732977569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_870732921536023739754807103419461 : Nat.Prime 870732921536023739754807103419461 := by
  refine lucas_primality 870732921536023739754807103419461 (3 : ZMod 870732921536023739754807103419461) ?_ (fun q hq hd => ?_)
  · rw [show 870732921536023739754807103419461 - 1 = 870732921536023739754807103419460 from by norm_num]
    reduce_mod_char
  · have e : 870732921536023739754807103419461 - 1 = [2 ^ 2, 5 ^ 1, 37 ^ 1, 709 ^ 1, 17333 ^ 1, 2277553 ^ 1, 42040200732977569 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (870732921536023739754807103419461 - 1) / 2 = 435366460768011869877403551709730 from by norm_num]
      have h2 : (3 : ZMod 870732921536023739754807103419461) ^ 435366460768011869877403551709730 = ((870732921536023739754807103419460 : ℕ) : ZMod 870732921536023739754807103419461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (870732921536023739754807103419461 - 1) / 5 = 174146584307204747950961420683892 from by norm_num]
      have h2 : (3 : ZMod 870732921536023739754807103419461) ^ 174146584307204747950961420683892 = ((527996754206497071662843467512489 : ℕ) : ZMod 870732921536023739754807103419461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (870732921536023739754807103419461 - 1) / 37 = 23533322203676317290670462254580 from by norm_num]
      have h2 : (3 : ZMod 870732921536023739754807103419461) ^ 23533322203676317290670462254580 = ((131883989031125476574062242917178 : ℕ) : ZMod 870732921536023739754807103419461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (870732921536023739754807103419461 - 1) / 709 = 1228114134747565218271942317940 from by norm_num]
      have h2 : (3 : ZMod 870732921536023739754807103419461) ^ 1228114134747565218271942317940 = ((196390716932731106987480852960493 : ℕ) : ZMod 870732921536023739754807103419461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (870732921536023739754807103419461 - 1) / 17333 = 50235557695495513745733981620 from by norm_num]
      have h2 : (3 : ZMod 870732921536023739754807103419461) ^ 50235557695495513745733981620 = ((802507508041061009831002651760904 : ℕ) : ZMod 870732921536023739754807103419461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (870732921536023739754807103419461 - 1) / 2277553 = 382310717483204008756242820 from by norm_num]
      have h2 : (3 : ZMod 870732921536023739754807103419461) ^ 382310717483204008756242820 = ((35518862931569220354070060927017 : ℕ) : ZMod 870732921536023739754807103419461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_42040200732977569).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (870732921536023739754807103419461 - 1) / 42040200732977569 = 20711911607334340 from by norm_num]
      have h2 : (3 : ZMod 870732921536023739754807103419461) ^ 20711911607334340 = ((522523286736152239188608216190831 : ℕ) : ZMod 870732921536023739754807103419461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3217113304667527 : Nat.Prime 3217113304667527 := by
  refine lucas_primality 3217113304667527 (3 : ZMod 3217113304667527) ?_ (fun q hq hd => ?_)
  · rw [show 3217113304667527 - 1 = 3217113304667526 from by norm_num]
    reduce_mod_char
  · have e : 3217113304667527 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 151 ^ 1, 218423 ^ 1, 1477907 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3217113304667527 - 1) / 2 = 1608556652333763 from by norm_num]
      have h2 : (3 : ZMod 3217113304667527) ^ 1608556652333763 = ((3217113304667526 : ℕ) : ZMod 3217113304667527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3217113304667527 - 1) / 3 = 1072371101555842 from by norm_num]
      have h2 : (3 : ZMod 3217113304667527) ^ 1072371101555842 = ((1406005820146146 : ℕ) : ZMod 3217113304667527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3217113304667527 - 1) / 11 = 292464845878866 from by norm_num]
      have h2 : (3 : ZMod 3217113304667527) ^ 292464845878866 = ((1143804695139338 : ℕ) : ZMod 3217113304667527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3217113304667527 - 1) / 151 = 21305386123626 from by norm_num]
      have h2 : (3 : ZMod 3217113304667527) ^ 21305386123626 = ((1477547575255170 : ℕ) : ZMod 3217113304667527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3217113304667527 - 1) / 218423 = 14728821162 from by norm_num]
      have h2 : (3 : ZMod 3217113304667527) ^ 14728821162 = ((464516661890350 : ℕ) : ZMod 3217113304667527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3217113304667527 - 1) / 1477907 = 2176803618 from by norm_num]
      have h2 : (3 : ZMod 3217113304667527) ^ 2176803618 = ((872544218523289 : ℕ) : ZMod 3217113304667527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_597755827652922384925757 : Nat.Prime 597755827652922384925757 := by
  refine lucas_primality 597755827652922384925757 (2 : ZMod 597755827652922384925757) ?_ (fun q hq hd => ?_)
  · rw [show 597755827652922384925757 - 1 = 597755827652922384925756 from by norm_num]
    reduce_mod_char
  · have e : 597755827652922384925757 - 1 = [2 ^ 2, 19 ^ 1, 1069 ^ 1, 2287 ^ 1, 3217113304667527 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (597755827652922384925757 - 1) / 2 = 298877913826461192462878 from by norm_num]
      have h2 : (2 : ZMod 597755827652922384925757) ^ 298877913826461192462878 = ((597755827652922384925756 : ℕ) : ZMod 597755827652922384925757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (597755827652922384925757 - 1) / 19 = 31460833034364336048724 from by norm_num]
      have h2 : (2 : ZMod 597755827652922384925757) ^ 31460833034364336048724 = ((309768735175902672475273 : ℕ) : ZMod 597755827652922384925757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (597755827652922384925757 - 1) / 1069 = 559172897710872202924 from by norm_num]
      have h2 : (2 : ZMod 597755827652922384925757) ^ 559172897710872202924 = ((367401285283806075701503 : ℕ) : ZMod 597755827652922384925757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (597755827652922384925757 - 1) / 2287 = 261371153324408563588 from by norm_num]
      have h2 : (2 : ZMod 597755827652922384925757) ^ 261371153324408563588 = ((279862171845343878316615 : ℕ) : ZMod 597755827652922384925757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3217113304667527).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (597755827652922384925757 - 1) / 3217113304667527 = 185805028 from by norm_num]
      have h2 : (2 : ZMod 597755827652922384925757) ^ 185805028 = ((401188423697501206975227 : ℕ) : ZMod 597755827652922384925757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_223560679542192971962233119 : Nat.Prime 223560679542192971962233119 := by
  refine lucas_primality 223560679542192971962233119 (7 : ZMod 223560679542192971962233119) ?_ (fun q hq hd => ?_)
  · rw [show 223560679542192971962233119 - 1 = 223560679542192971962233118 from by norm_num]
    reduce_mod_char
  · have e : 223560679542192971962233119 - 1 = [2 ^ 1, 11 ^ 1, 17 ^ 1, 597755827652922384925757 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (223560679542192971962233119 - 1) / 2 = 111780339771096485981116559 from by norm_num]
      have h2 : (7 : ZMod 223560679542192971962233119) ^ 111780339771096485981116559 = ((223560679542192971962233118 : ℕ) : ZMod 223560679542192971962233119) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (223560679542192971962233119 - 1) / 11 = 20323698140199361087475738 from by norm_num]
      have h2 : (7 : ZMod 223560679542192971962233119) ^ 20323698140199361087475738 = ((219840250009481037720342669 : ℕ) : ZMod 223560679542192971962233119) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (223560679542192971962233119 - 1) / 17 = 13150628208364292468366654 from by norm_num]
      have h2 : (7 : ZMod 223560679542192971962233119) ^ 13150628208364292468366654 = ((221374495348043419151622667 : ℕ) : ZMod 223560679542192971962233119) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_597755827652922384925757).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (223560679542192971962233119 - 1) / 597755827652922384925757 = 374 from by norm_num]
      have h2 : (7 : ZMod 223560679542192971962233119) ^ 374 = ((11814204531457952609142934 : ℕ) : ZMod 223560679542192971962233119) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_31072352777637469858310183672941789 : Nat.Prime 31072352777637469858310183672941789 := by
  refine lucas_primality 31072352777637469858310183672941789 (6 : ZMod 31072352777637469858310183672941789) ?_ (fun q hq hd => ?_)
  · rw [show 31072352777637469858310183672941789 - 1 = 31072352777637469858310183672941788 from by norm_num]
    reduce_mod_char
  · have e : 31072352777637469858310183672941789 - 1 = [2 ^ 2, 3 ^ 1, 89 ^ 1, 181 ^ 1, 719 ^ 1, 223560679542192971962233119 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31072352777637469858310183672941789 - 1) / 2 = 15536176388818734929155091836470894 from by norm_num]
      have h2 : (6 : ZMod 31072352777637469858310183672941789) ^ 15536176388818734929155091836470894 = ((31072352777637469858310183672941788 : ℕ) : ZMod 31072352777637469858310183672941789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31072352777637469858310183672941789 - 1) / 3 = 10357450925879156619436727890980596 from by norm_num]
      have h2 : (6 : ZMod 31072352777637469858310183672941789) ^ 10357450925879156619436727890980596 = ((19795394506765172806821847013296363 : ℕ) : ZMod 31072352777637469858310183672941789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31072352777637469858310183672941789 - 1) / 89 = 349127559299297414138316670482492 from by norm_num]
      have h2 : (6 : ZMod 31072352777637469858310183672941789) ^ 349127559299297414138316670482492 = ((27331326815436969573889727977543769 : ℕ) : ZMod 31072352777637469858310183672941789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31072352777637469858310183672941789 - 1) / 181 = 171670457335013645626023114215148 from by norm_num]
      have h2 : (6 : ZMod 31072352777637469858310183672941789) ^ 171670457335013645626023114215148 = ((9561351776475428627457563979134489 : ℕ) : ZMod 31072352777637469858310183672941789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31072352777637469858310183672941789 - 1) / 719 = 43216067840942239024075359767652 from by norm_num]
      have h2 : (6 : ZMod 31072352777637469858310183672941789) ^ 43216067840942239024075359767652 = ((16454831148934703449054576387906331 : ℕ) : ZMod 31072352777637469858310183672941789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_223560679542192971962233119).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31072352777637469858310183672941789 - 1) / 223560679542192971962233119 = 138988452 from by norm_num]
      have h2 : (6 : ZMod 31072352777637469858310183672941789) ^ 138988452 = ((12174985070924893021429867389051482 : ℕ) : ZMod 31072352777637469858310183672941789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_233117587 : Nat.Prime 233117587 := by
  refine lucas_primality 233117587 (3 : ZMod 233117587) ?_ (fun q hq hd => ?_)
  · rw [show 233117587 - 1 = 233117586 from by norm_num]
    reduce_mod_char
  · have e : 233117587 - 1 = [2 ^ 1, 3 ^ 2, 13 ^ 2, 197 ^ 1, 389 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (233117587 - 1) / 2 = 116558793 from by norm_num]
      have h2 : (3 : ZMod 233117587) ^ 116558793 = ((233117586 : ℕ) : ZMod 233117587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (233117587 - 1) / 3 = 77705862 from by norm_num]
      have h2 : (3 : ZMod 233117587) ^ 77705862 = ((76525089 : ℕ) : ZMod 233117587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (233117587 - 1) / 13 = 17932122 from by norm_num]
      have h2 : (3 : ZMod 233117587) ^ 17932122 = ((86043296 : ℕ) : ZMod 233117587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (233117587 - 1) / 197 = 1183338 from by norm_num]
      have h2 : (3 : ZMod 233117587) ^ 1183338 = ((226730864 : ℕ) : ZMod 233117587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (233117587 - 1) / 389 = 599274 from by norm_num]
      have h2 : (3 : ZMod 233117587) ^ 599274 = ((26073434 : ℕ) : ZMod 233117587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11538944790333429277 : Nat.Prime 11538944790333429277 := by
  refine lucas_primality 11538944790333429277 (5 : ZMod 11538944790333429277) ?_ (fun q hq hd => ?_)
  · rw [show 11538944790333429277 - 1 = 11538944790333429276 from by norm_num]
    reduce_mod_char
  · have e : 11538944790333429277 - 1 = [2 ^ 2, 3 ^ 3, 29 ^ 1, 9547 ^ 1, 30829 ^ 1, 12517511 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11538944790333429277 - 1) / 2 = 5769472395166714638 from by norm_num]
      have h2 : (5 : ZMod 11538944790333429277) ^ 5769472395166714638 = ((11538944790333429276 : ℕ) : ZMod 11538944790333429277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11538944790333429277 - 1) / 3 = 3846314930111143092 from by norm_num]
      have h2 : (5 : ZMod 11538944790333429277) ^ 3846314930111143092 = ((2274965222370518492 : ℕ) : ZMod 11538944790333429277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11538944790333429277 - 1) / 29 = 397894647942532044 from by norm_num]
      have h2 : (5 : ZMod 11538944790333429277) ^ 397894647942532044 = ((7528646378209405477 : ℕ) : ZMod 11538944790333429277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11538944790333429277 - 1) / 9547 = 1208646149610708 from by norm_num]
      have h2 : (5 : ZMod 11538944790333429277) ^ 1208646149610708 = ((1787544885910254352 : ℕ) : ZMod 11538944790333429277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11538944790333429277 - 1) / 30829 = 374288649983244 from by norm_num]
      have h2 : (5 : ZMod 11538944790333429277) ^ 374288649983244 = ((11010873036830569991 : ℕ) : ZMod 11538944790333429277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11538944790333429277 - 1) / 12517511 = 921824218116 from by norm_num]
      have h2 : (5 : ZMod 11538944790333429277) ^ 921824218116 = ((10101291068594871545 : ℕ) : ZMod 11538944790333429277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_276934674968002302649 : Nat.Prime 276934674968002302649 := by
  refine lucas_primality 276934674968002302649 (13 : ZMod 276934674968002302649) ?_ (fun q hq hd => ?_)
  · rw [show 276934674968002302649 - 1 = 276934674968002302648 from by norm_num]
    reduce_mod_char
  · have e : 276934674968002302649 - 1 = [2 ^ 3, 3 ^ 1, 11538944790333429277 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (276934674968002302649 - 1) / 2 = 138467337484001151324 from by norm_num]
      have h2 : (13 : ZMod 276934674968002302649) ^ 138467337484001151324 = ((276934674968002302648 : ℕ) : ZMod 276934674968002302649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (276934674968002302649 - 1) / 3 = 92311558322667434216 from by norm_num]
      have h2 : (13 : ZMod 276934674968002302649) ^ 92311558322667434216 = ((35519258808659896813 : ℕ) : ZMod 276934674968002302649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_11538944790333429277).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (276934674968002302649 - 1) / 11538944790333429277 = 24 from by norm_num]
      have h2 : (13 : ZMod 276934674968002302649) ^ 24 = ((222462161991508173242 : ℕ) : ZMod 276934674968002302649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_381615982105907173050323 : Nat.Prime 381615982105907173050323 := by
  refine lucas_primality 381615982105907173050323 (2 : ZMod 381615982105907173050323) ?_ (fun q hq hd => ?_)
  · rw [show 381615982105907173050323 - 1 = 381615982105907173050322 from by norm_num]
    reduce_mod_char
  · have e : 381615982105907173050323 - 1 = [2 ^ 1, 13 ^ 1, 53 ^ 1, 276934674968002302649 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381615982105907173050323 - 1) / 2 = 190807991052953586525161 from by norm_num]
      have h2 : (2 : ZMod 381615982105907173050323) ^ 190807991052953586525161 = ((381615982105907173050322 : ℕ) : ZMod 381615982105907173050323) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381615982105907173050323 - 1) / 13 = 29355075546608244080794 from by norm_num]
      have h2 : (2 : ZMod 381615982105907173050323) ^ 29355075546608244080794 = ((8359958562159565916092 : ℕ) : ZMod 381615982105907173050323) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381615982105907173050323 - 1) / 53 = 7200301549168059868874 from by norm_num]
      have h2 : (2 : ZMod 381615982105907173050323) ^ 7200301549168059868874 = ((159332716925506033041243 : ℕ) : ZMod 381615982105907173050323) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_276934674968002302649).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381615982105907173050323 - 1) / 276934674968002302649 = 1378 from by norm_num]
      have h2 : (2 : ZMod 381615982105907173050323) ^ 1378 = ((107302174308747250219107 : ℕ) : ZMod 381615982105907173050323) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_155046904371518383134460036224501936457 : Nat.Prime 155046904371518383134460036224501936457 := by
  refine lucas_primality 155046904371518383134460036224501936457 (5 : ZMod 155046904371518383134460036224501936457) ?_ (fun q hq hd => ?_)
  · rw [show 155046904371518383134460036224501936457 - 1 = 155046904371518383134460036224501936456 from by norm_num]
    reduce_mod_char
  · have e : 155046904371518383134460036224501936457 - 1 = [2 ^ 3, 3 ^ 1, 101 ^ 1, 719 ^ 1, 233117587 ^ 1, 381615982105907173050323 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155046904371518383134460036224501936457 - 1) / 2 = 77523452185759191567230018112250968228 from by norm_num]
      have h2 : (5 : ZMod 155046904371518383134460036224501936457) ^ 77523452185759191567230018112250968228 = ((155046904371518383134460036224501936456 : ℕ) : ZMod 155046904371518383134460036224501936457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155046904371518383134460036224501936457 - 1) / 3 = 51682301457172794378153345408167312152 from by norm_num]
      have h2 : (5 : ZMod 155046904371518383134460036224501936457) ^ 51682301457172794378153345408167312152 = ((10099811695111982755589916214092818006 : ℕ) : ZMod 155046904371518383134460036224501936457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155046904371518383134460036224501936457 - 1) / 101 = 1535117865064538446875841942816850856 from by norm_num]
      have h2 : (5 : ZMod 155046904371518383134460036224501936457) ^ 1535117865064538446875841942816850856 = ((27985864010397550826339678813250757333 : ℕ) : ZMod 155046904371518383134460036224501936457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155046904371518383134460036224501936457 - 1) / 719 = 215642426107814162913018131049376824 from by norm_num]
      have h2 : (5 : ZMod 155046904371518383134460036224501936457) ^ 215642426107814162913018131049376824 = ((51668673796093177892262994651305664462 : ℕ) : ZMod 155046904371518383134460036224501936457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_233117587).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155046904371518383134460036224501936457 - 1) / 233117587 = 665101704109172951993793742488 from by norm_num]
      have h2 : (5 : ZMod 155046904371518383134460036224501936457) ^ 665101704109172951993793742488 = ((13362890607316500319251885485359114309 : ℕ) : ZMod 155046904371518383134460036224501936457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_381615982105907173050323).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155046904371518383134460036224501936457 - 1) / 381615982105907173050323 = 406290385208472 from by norm_num]
      have h2 : (5 : ZMod 155046904371518383134460036224501936457) ^ 406290385208472 = ((95604220815896605047607903332170769431 : ℕ) : ZMod 155046904371518383134460036224501936457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_85547875627 : Nat.Prime 85547875627 := by
  refine lucas_primality 85547875627 (2 : ZMod 85547875627) ?_ (fun q hq hd => ?_)
  · rw [show 85547875627 - 1 = 85547875626 from by norm_num]
    reduce_mod_char
  · have e : 85547875627 - 1 = [2 ^ 1, 3 ^ 3, 17 ^ 1, 1601 ^ 1, 58207 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85547875627 - 1) / 2 = 42773937813 from by norm_num]
      have h2 : (2 : ZMod 85547875627) ^ 42773937813 = ((85547875626 : ℕ) : ZMod 85547875627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85547875627 - 1) / 3 = 28515958542 from by norm_num]
      have h2 : (2 : ZMod 85547875627) ^ 28515958542 = ((82463254662 : ℕ) : ZMod 85547875627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85547875627 - 1) / 17 = 5032227978 from by norm_num]
      have h2 : (2 : ZMod 85547875627) ^ 5032227978 = ((83158327767 : ℕ) : ZMod 85547875627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85547875627 - 1) / 1601 = 53434026 from by norm_num]
      have h2 : (2 : ZMod 85547875627) ^ 53434026 = ((81143864259 : ℕ) : ZMod 85547875627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85547875627 - 1) / 58207 = 1469718 from by norm_num]
      have h2 : (2 : ZMod 85547875627) ^ 1469718 = ((60026723509 : ℕ) : ZMod 85547875627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_122781683 : Nat.Prime 122781683 := by
  refine lucas_primality 122781683 (2 : ZMod 122781683) ?_ (fun q hq hd => ?_)
  · rw [show 122781683 - 1 = 122781682 from by norm_num]
    reduce_mod_char
  · have e : 122781683 - 1 = [2 ^ 1, 23 ^ 1, 2669167 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (122781683 - 1) / 2 = 61390841 from by norm_num]
      have h2 : (2 : ZMod 122781683) ^ 61390841 = ((122781682 : ℕ) : ZMod 122781683) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (122781683 - 1) / 23 = 5338334 from by norm_num]
      have h2 : (2 : ZMod 122781683) ^ 5338334 = ((116099098 : ℕ) : ZMod 122781683) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (122781683 - 1) / 2669167 = 46 from by norm_num]
      have h2 : (2 : ZMod 122781683) ^ 46 = ((106016704 : ℕ) : ZMod 122781683) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_327335966879 : Nat.Prime 327335966879 := by
  refine lucas_primality 327335966879 (11 : ZMod 327335966879) ?_ (fun q hq hd => ?_)
  · rw [show 327335966879 - 1 = 327335966878 from by norm_num]
    reduce_mod_char
  · have e : 327335966879 - 1 = [2 ^ 1, 31 ^ 1, 43 ^ 1, 122781683 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (327335966879 - 1) / 2 = 163667983439 from by norm_num]
      have h2 : (11 : ZMod 327335966879) ^ 163667983439 = ((327335966878 : ℕ) : ZMod 327335966879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (327335966879 - 1) / 31 = 10559224738 from by norm_num]
      have h2 : (11 : ZMod 327335966879) ^ 10559224738 = ((320690973376 : ℕ) : ZMod 327335966879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (327335966879 - 1) / 43 = 7612464346 from by norm_num]
      have h2 : (11 : ZMod 327335966879) ^ 7612464346 = ((97404254104 : ℕ) : ZMod 327335966879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_122781683).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (327335966879 - 1) / 122781683 = 2666 from by norm_num]
      have h2 : (11 : ZMod 327335966879) ^ 2666 = ((311153372528 : ℕ) : ZMod 327335966879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_654671933759 : Nat.Prime 654671933759 := by
  refine lucas_primality 654671933759 (7 : ZMod 654671933759) ?_ (fun q hq hd => ?_)
  · rw [show 654671933759 - 1 = 654671933758 from by norm_num]
    reduce_mod_char
  · have e : 654671933759 - 1 = [2 ^ 1, 327335966879 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (654671933759 - 1) / 2 = 327335966879 from by norm_num]
      have h2 : (7 : ZMod 654671933759) ^ 327335966879 = ((654671933758 : ℕ) : ZMod 654671933759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_327335966879).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (654671933759 - 1) / 327335966879 = 2 from by norm_num]
      have h2 : (7 : ZMod 654671933759) ^ 2 = ((49 : ℕ) : ZMod 654671933759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_38247249349903277 : Nat.Prime 38247249349903277 := by
  refine lucas_primality 38247249349903277 (2 : ZMod 38247249349903277) ?_ (fun q hq hd => ?_)
  · rw [show 38247249349903277 - 1 = 38247249349903276 from by norm_num]
    reduce_mod_char
  · have e : 38247249349903277 - 1 = [2 ^ 2, 29 ^ 1, 173 ^ 1, 261101 ^ 1, 7299407 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38247249349903277 - 1) / 2 = 19123624674951638 from by norm_num]
      have h2 : (2 : ZMod 38247249349903277) ^ 19123624674951638 = ((38247249349903276 : ℕ) : ZMod 38247249349903277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38247249349903277 - 1) / 29 = 1318870667238044 from by norm_num]
      have h2 : (2 : ZMod 38247249349903277) ^ 1318870667238044 = ((9530293465180898 : ℕ) : ZMod 38247249349903277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38247249349903277 - 1) / 173 = 221082366184412 from by norm_num]
      have h2 : (2 : ZMod 38247249349903277) ^ 221082366184412 = ((3188366925805477 : ℕ) : ZMod 38247249349903277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38247249349903277 - 1) / 261101 = 146484499676 from by norm_num]
      have h2 : (2 : ZMod 38247249349903277) ^ 146484499676 = ((824272320278606 : ℕ) : ZMod 38247249349903277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38247249349903277 - 1) / 7299407 = 5239774868 from by norm_num]
      have h2 : (2 : ZMod 38247249349903277) ^ 5239774868 = ((16730121743082212 : ℕ) : ZMod 38247249349903277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_47125485797450123694087133934414923333943 : Nat.Prime 47125485797450123694087133934414923333943 := by
  refine lucas_primality 47125485797450123694087133934414923333943 (5 : ZMod 47125485797450123694087133934414923333943) ?_ (fun q hq hd => ?_)
  · rw [show 47125485797450123694087133934414923333943 - 1 = 47125485797450123694087133934414923333942 from by norm_num]
    reduce_mod_char
  · have e : 47125485797450123694087133934414923333943 - 1 = [2 ^ 1, 11 ^ 1, 85547875627 ^ 1, 654671933759 ^ 1, 38247249349903277 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47125485797450123694087133934414923333943 - 1) / 2 = 23562742898725061847043566967207461666971 from by norm_num]
      have h2 : (5 : ZMod 47125485797450123694087133934414923333943) ^ 23562742898725061847043566967207461666971 = ((47125485797450123694087133934414923333942 : ℕ) : ZMod 47125485797450123694087133934414923333943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47125485797450123694087133934414923333943 - 1) / 11 = 4284135072495465790371557630401356666722 from by norm_num]
      have h2 : (5 : ZMod 47125485797450123694087133934414923333943) ^ 4284135072495465790371557630401356666722 = ((9600711552627834334410020766021225762178 : ℕ) : ZMod 47125485797450123694087133934414923333943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_85547875627).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47125485797450123694087133934414923333943 - 1) / 85547875627 = 550866815243004347410422621346 from by norm_num]
      have h2 : (5 : ZMod 47125485797450123694087133934414923333943) ^ 550866815243004347410422621346 = ((27275147467850002573901714920818123927231 : ℕ) : ZMod 47125485797450123694087133934414923333943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_654671933759).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47125485797450123694087133934414923333943 - 1) / 654671933759 = 71983360470128407196066052938 from by norm_num]
      have h2 : (5 : ZMod 47125485797450123694087133934414923333943) ^ 71983360470128407196066052938 = ((16987092902667359910915056235531801409076 : ℕ) : ZMod 47125485797450123694087133934414923333943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_38247249349903277).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47125485797450123694087133934414923333943 - 1) / 38247249349903277 = 1232127449645455321021646 from by norm_num]
      have h2 : (5 : ZMod 47125485797450123694087133934414923333943) ^ 1232127449645455321021646 = ((44733597899035259647635560643135734614548 : ℕ) : ZMod 47125485797450123694087133934414923333943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_73723298483474163307524688675534443723313764973 : Nat.Prime 73723298483474163307524688675534443723313764973 := by
  refine lucas_primality 73723298483474163307524688675534443723313764973 (5 : ZMod 73723298483474163307524688675534443723313764973) ?_ (fun q hq hd => ?_)
  · rw [show 73723298483474163307524688675534443723313764973 - 1 = 73723298483474163307524688675534443723313764972 from by norm_num]
    reduce_mod_char
  · have e : 73723298483474163307524688675534443723313764973 - 1 = [2 ^ 2, 3 ^ 1, 130367 ^ 1, 47125485797450123694087133934414923333943 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (73723298483474163307524688675534443723313764973 - 1) / 2 = 36861649241737081653762344337767221861656882486 from by norm_num]
      have h2 : (5 : ZMod 73723298483474163307524688675534443723313764973) ^ 36861649241737081653762344337767221861656882486 = ((73723298483474163307524688675534443723313764972 : ℕ) : ZMod 73723298483474163307524688675534443723313764973) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (73723298483474163307524688675534443723313764973 - 1) / 3 = 24574432827824721102508229558511481241104588324 from by norm_num]
      have h2 : (5 : ZMod 73723298483474163307524688675534443723313764973) ^ 24574432827824721102508229558511481241104588324 = ((64162495899897632862314006296067050332108366839 : ℕ) : ZMod 73723298483474163307524688675534443723313764973) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (73723298483474163307524688675534443723313764973 - 1) / 130367 = 565505829569401484329045607212979080007316 from by norm_num]
      have h2 : (5 : ZMod 73723298483474163307524688675534443723313764973) ^ 565505829569401484329045607212979080007316 = ((42742919488755698240490890043831031641056054634 : ℕ) : ZMod 73723298483474163307524688675534443723313764973) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_47125485797450123694087133934414923333943).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (73723298483474163307524688675534443723313764973 - 1) / 47125485797450123694087133934414923333943 = 1564404 from by norm_num]
      have h2 : (5 : ZMod 73723298483474163307524688675534443723313764973) ^ 1564404 = ((57413907368686298702108747213208616403816481311 : ℕ) : ZMod 73723298483474163307524688675534443723313764973) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_857549407959771467593127178673816649389585714165937 : Nat.Prime 857549407959771467593127178673816649389585714165937 := by
  refine lucas_primality 857549407959771467593127178673816649389585714165937 (3 : ZMod 857549407959771467593127178673816649389585714165937) ?_ (fun q hq hd => ?_)
  · rw [show 857549407959771467593127178673816649389585714165937 - 1 = 857549407959771467593127178673816649389585714165936 from by norm_num]
    reduce_mod_char
  · have e : 857549407959771467593127178673816649389585714165937 - 1 = [2 ^ 4, 727 ^ 1, 73723298483474163307524688675534443723313764973 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (857549407959771467593127178673816649389585714165937 - 1) / 2 = 428774703979885733796563589336908324694792857082968 from by norm_num]
      have h2 : (3 : ZMod 857549407959771467593127178673816649389585714165937) ^ 428774703979885733796563589336908324694792857082968 = ((857549407959771467593127178673816649389585714165936 : ℕ) : ZMod 857549407959771467593127178673816649389585714165937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (857549407959771467593127178673816649389585714165937 - 1) / 727 = 1179572775735586612920395018808551099573020239568 from by norm_num]
      have h2 : (3 : ZMod 857549407959771467593127178673816649389585714165937) ^ 1179572775735586612920395018808551099573020239568 = ((246387535496411248437195212092496347296199228486451 : ℕ) : ZMod 857549407959771467593127178673816649389585714165937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_73723298483474163307524688675534443723313764973).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (857549407959771467593127178673816649389585714165937 - 1) / 73723298483474163307524688675534443723313764973 = 11632 from by norm_num]
      have h2 : (3 : ZMod 857549407959771467593127178673816649389585714165937) ^ 11632 = ((651545926010895554782653062892815530178684756829356 : ℕ) : ZMod 857549407959771467593127178673816649389585714165937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_330909659 : Nat.Prime 330909659 := by
  refine lucas_primality 330909659 (2 : ZMod 330909659) ?_ (fun q hq hd => ?_)
  · rw [show 330909659 - 1 = 330909658 from by norm_num]
    reduce_mod_char
  · have e : 330909659 - 1 = [2 ^ 1, 17 ^ 1, 1567 ^ 1, 6211 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (330909659 - 1) / 2 = 165454829 from by norm_num]
      have h2 : (2 : ZMod 330909659) ^ 165454829 = ((330909658 : ℕ) : ZMod 330909659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (330909659 - 1) / 17 = 19465274 from by norm_num]
      have h2 : (2 : ZMod 330909659) ^ 19465274 = ((198712332 : ℕ) : ZMod 330909659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (330909659 - 1) / 1567 = 211174 from by norm_num]
      have h2 : (2 : ZMod 330909659) ^ 211174 = ((250325604 : ℕ) : ZMod 330909659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (330909659 - 1) / 6211 = 53278 from by norm_num]
      have h2 : (2 : ZMod 330909659) ^ 53278 = ((104633905 : ℕ) : ZMod 330909659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4320559493 : Nat.Prime 4320559493 := by
  refine lucas_primality 4320559493 (2 : ZMod 4320559493) ?_ (fun q hq hd => ?_)
  · rw [show 4320559493 - 1 = 4320559492 from by norm_num]
    reduce_mod_char
  · have e : 4320559493 - 1 = [2 ^ 2, 19 ^ 1, 2371 ^ 1, 23977 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4320559493 - 1) / 2 = 2160279746 from by norm_num]
      have h2 : (2 : ZMod 4320559493) ^ 2160279746 = ((4320559492 : ℕ) : ZMod 4320559493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4320559493 - 1) / 19 = 227397868 from by norm_num]
      have h2 : (2 : ZMod 4320559493) ^ 227397868 = ((2123938695 : ℕ) : ZMod 4320559493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4320559493 - 1) / 2371 = 1822252 from by norm_num]
      have h2 : (2 : ZMod 4320559493) ^ 1822252 = ((2106851626 : ℕ) : ZMod 4320559493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4320559493 - 1) / 23977 = 180196 from by norm_num]
      have h2 : (2 : ZMod 4320559493) ^ 180196 = ((2053080926 : ℕ) : ZMod 4320559493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8173756897 : Nat.Prime 8173756897 := by
  refine lucas_primality 8173756897 (5 : ZMod 8173756897) ?_ (fun q hq hd => ?_)
  · rw [show 8173756897 - 1 = 8173756896 from by norm_num]
    reduce_mod_char
  · have e : 8173756897 - 1 = [2 ^ 5, 3 ^ 1, 193 ^ 1, 441157 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8173756897 - 1) / 2 = 4086878448 from by norm_num]
      have h2 : (5 : ZMod 8173756897) ^ 4086878448 = ((8173756896 : ℕ) : ZMod 8173756897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8173756897 - 1) / 3 = 2724585632 from by norm_num]
      have h2 : (5 : ZMod 8173756897) ^ 2724585632 = ((4457855232 : ℕ) : ZMod 8173756897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8173756897 - 1) / 193 = 42351072 from by norm_num]
      have h2 : (5 : ZMod 8173756897) ^ 42351072 = ((4636460282 : ℕ) : ZMod 8173756897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8173756897 - 1) / 441157 = 18528 from by norm_num]
      have h2 : (5 : ZMod 8173756897) ^ 18528 = ((4621809803 : ℕ) : ZMod 8173756897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_245212706911 : Nat.Prime 245212706911 := by
  refine lucas_primality 245212706911 (6 : ZMod 245212706911) ?_ (fun q hq hd => ?_)
  · rw [show 245212706911 - 1 = 245212706910 from by norm_num]
    reduce_mod_char
  · have e : 245212706911 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 8173756897 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (245212706911 - 1) / 2 = 122606353455 from by norm_num]
      have h2 : (6 : ZMod 245212706911) ^ 122606353455 = ((245212706910 : ℕ) : ZMod 245212706911) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (245212706911 - 1) / 3 = 81737568970 from by norm_num]
      have h2 : (6 : ZMod 245212706911) ^ 81737568970 = ((201989118915 : ℕ) : ZMod 245212706911) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (245212706911 - 1) / 5 = 49042541382 from by norm_num]
      have h2 : (6 : ZMod 245212706911) ^ 49042541382 = ((228070010271 : ℕ) : ZMod 245212706911) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_8173756897).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (245212706911 - 1) / 8173756897 = 30 from by norm_num]
      have h2 : (6 : ZMod 245212706911) ^ 30 = ((158647195258 : ℕ) : ZMod 245212706911) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8414022072483953011773050209369 : Nat.Prime 8414022072483953011773050209369 := by
  refine lucas_primality 8414022072483953011773050209369 (11 : ZMod 8414022072483953011773050209369) ?_ (fun q hq hd => ?_)
  · rw [show 8414022072483953011773050209369 - 1 = 8414022072483953011773050209368 from by norm_num]
    reduce_mod_char
  · have e : 8414022072483953011773050209369 - 1 = [2 ^ 3, 3 ^ 1, 330909659 ^ 1, 4320559493 ^ 1, 245212706911 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8414022072483953011773050209369 - 1) / 2 = 4207011036241976505886525104684 from by norm_num]
      have h2 : (11 : ZMod 8414022072483953011773050209369) ^ 4207011036241976505886525104684 = ((8414022072483953011773050209368 : ℕ) : ZMod 8414022072483953011773050209369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8414022072483953011773050209369 - 1) / 3 = 2804674024161317670591016736456 from by norm_num]
      have h2 : (11 : ZMod 8414022072483953011773050209369) ^ 2804674024161317670591016736456 = ((1014375290259510524755515737209 : ℕ) : ZMod 8414022072483953011773050209369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_330909659).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8414022072483953011773050209369 - 1) / 330909659 = 25426946127565146146952 from by norm_num]
      have h2 : (11 : ZMod 8414022072483953011773050209369) ^ 25426946127565146146952 = ((7027332688512263907579184402760 : ℕ) : ZMod 8414022072483953011773050209369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4320559493).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8414022072483953011773050209369 - 1) / 4320559493 = 1947438077433262880376 from by norm_num]
      have h2 : (11 : ZMod 8414022072483953011773050209369) ^ 1947438077433262880376 = ((3837049124342859404026261515138 : ℕ) : ZMod 8414022072483953011773050209369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_245212706911).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8414022072483953011773050209369 - 1) / 245212706911 = 34313156844428229288 from by norm_num]
      have h2 : (11 : ZMod 8414022072483953011773050209369) ^ 34313156844428229288 = ((5418100086533025921761331141918 : ℕ) : ZMod 8414022072483953011773050209369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_92402237 : Nat.Prime 92402237 := by
  refine lucas_primality 92402237 (2 : ZMod 92402237) ?_ (fun q hq hd => ?_)
  · rw [show 92402237 - 1 = 92402236 from by norm_num]
    reduce_mod_char
  · have e : 92402237 - 1 = [2 ^ 2, 29 ^ 1, 796571 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92402237 - 1) / 2 = 46201118 from by norm_num]
      have h2 : (2 : ZMod 92402237) ^ 46201118 = ((92402236 : ℕ) : ZMod 92402237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92402237 - 1) / 29 = 3186284 from by norm_num]
      have h2 : (2 : ZMod 92402237) ^ 3186284 = ((50653633 : ℕ) : ZMod 92402237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92402237 - 1) / 796571 = 116 from by norm_num]
      have h2 : (2 : ZMod 92402237) ^ 116 = ((54461628 : ℕ) : ZMod 92402237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2053903303 : Nat.Prime 2053903303 := by
  refine lucas_primality 2053903303 (3 : ZMod 2053903303) ?_ (fun q hq hd => ?_)
  · rw [show 2053903303 - 1 = 2053903302 from by norm_num]
    reduce_mod_char
  · have e : 2053903303 - 1 = [2 ^ 1, 3 ^ 2, 11 ^ 1, 10373249 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2053903303 - 1) / 2 = 1026951651 from by norm_num]
      have h2 : (3 : ZMod 2053903303) ^ 1026951651 = ((2053903302 : ℕ) : ZMod 2053903303) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2053903303 - 1) / 3 = 684634434 from by norm_num]
      have h2 : (3 : ZMod 2053903303) ^ 684634434 = ((894539702 : ℕ) : ZMod 2053903303) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2053903303 - 1) / 11 = 186718482 from by norm_num]
      have h2 : (3 : ZMod 2053903303) ^ 186718482 = ((1143412210 : ℕ) : ZMod 2053903303) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2053903303 - 1) / 10373249 = 198 from by norm_num]
      have h2 : (3 : ZMod 2053903303) ^ 198 = ((735375037 : ℕ) : ZMod 2053903303) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4934416754251109087 : Nat.Prime 4934416754251109087 := by
  refine lucas_primality 4934416754251109087 (5 : ZMod 4934416754251109087) ?_ (fun q hq hd => ?_)
  · rw [show 4934416754251109087 - 1 = 4934416754251109086 from by norm_num]
    reduce_mod_char
  · have e : 4934416754251109087 - 1 = [2 ^ 1, 13 ^ 1, 92402237 ^ 1, 2053903303 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4934416754251109087 - 1) / 2 = 2467208377125554543 from by norm_num]
      have h2 : (5 : ZMod 4934416754251109087) ^ 2467208377125554543 = ((4934416754251109086 : ℕ) : ZMod 4934416754251109087) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4934416754251109087 - 1) / 13 = 379570519557777622 from by norm_num]
      have h2 : (5 : ZMod 4934416754251109087) ^ 379570519557777622 = ((666958683067319307 : ℕ) : ZMod 4934416754251109087) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_92402237).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4934416754251109087 - 1) / 92402237 = 53401485878 from by norm_num]
      have h2 : (5 : ZMod 4934416754251109087) ^ 53401485878 = ((3283666983646789288 : ℕ) : ZMod 4934416754251109087) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2053903303).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4934416754251109087 - 1) / 2053903303 = 2402458162 from by norm_num]
      have h2 : (5 : ZMod 4934416754251109087) ^ 2402458162 = ((1708769226041722743 : ℕ) : ZMod 4934416754251109087) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1667832862936874871407 : Nat.Prime 1667832862936874871407 := by
  refine lucas_primality 1667832862936874871407 (5 : ZMod 1667832862936874871407) ?_ (fun q hq hd => ?_)
  · rw [show 1667832862936874871407 - 1 = 1667832862936874871406 from by norm_num]
    reduce_mod_char
  · have e : 1667832862936874871407 - 1 = [2 ^ 1, 13 ^ 2, 4934416754251109087 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1667832862936874871407 - 1) / 2 = 833916431468437435703 from by norm_num]
      have h2 : (5 : ZMod 1667832862936874871407) ^ 833916431468437435703 = ((1667832862936874871406 : ℕ) : ZMod 1667832862936874871407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1667832862936874871407 - 1) / 13 = 128294835610528836262 from by norm_num]
      have h2 : (5 : ZMod 1667832862936874871407) ^ 128294835610528836262 = ((993340248953505070039 : ℕ) : ZMod 1667832862936874871407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4934416754251109087).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1667832862936874871407 - 1) / 4934416754251109087 = 338 from by norm_num]
      have h2 : (5 : ZMod 1667832862936874871407) ^ 338 = ((810103016350477470629 : ℕ) : ZMod 1667832862936874871407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_205726455772006440377818607135775827053674474181634602781 : Nat.Prime 205726455772006440377818607135775827053674474181634602781 := by
  refine lucas_primality 205726455772006440377818607135775827053674474181634602781 (3 : ZMod 205726455772006440377818607135775827053674474181634602781) ?_ (fun q hq hd => ?_)
  · rw [show 205726455772006440377818607135775827053674474181634602781 - 1 = 205726455772006440377818607135775827053674474181634602780 from by norm_num]
    reduce_mod_char
  · have e : 205726455772006440377818607135775827053674474181634602781 - 1 = [2 ^ 2, 5 ^ 1, 733 ^ 1, 1667832862936874871407 ^ 1, 8414022072483953011773050209369 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (205726455772006440377818607135775827053674474181634602781 - 1) / 2 = 102863227886003220188909303567887913526837237090817301390 from by norm_num]
      have h2 : (3 : ZMod 205726455772006440377818607135775827053674474181634602781) ^ 102863227886003220188909303567887913526837237090817301390 = ((205726455772006440377818607135775827053674474181634602780 : ℕ) : ZMod 205726455772006440377818607135775827053674474181634602781) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (205726455772006440377818607135775827053674474181634602781 - 1) / 5 = 41145291154401288075563721427155165410734894836326920556 from by norm_num]
      have h2 : (3 : ZMod 205726455772006440377818607135775827053674474181634602781) ^ 41145291154401288075563721427155165410734894836326920556 = ((48618028557187248339929496321852668118045119991157950132 : ℕ) : ZMod 205726455772006440377818607135775827053674474181634602781) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (205726455772006440377818607135775827053674474181634602781 - 1) / 733 = 280663650439299372957460582722750105120974726032243660 from by norm_num]
      have h2 : (3 : ZMod 205726455772006440377818607135775827053674474181634602781) ^ 280663650439299372957460582722750105120974726032243660 = ((147257075725803953766841138507089787094160890503554689767 : ℕ) : ZMod 205726455772006440377818607135775827053674474181634602781) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1667832862936874871407).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (205726455772006440377818607135775827053674474181634602781 - 1) / 1667832862936874871407 = 123349563582614751152592916069349540 from by norm_num]
      have h2 : (3 : ZMod 205726455772006440377818607135775827053674474181634602781) ^ 123349563582614751152592916069349540 = ((66490446085469020240501872880217602337267402433353431388 : ℕ) : ZMod 205726455772006440377818607135775827053674474181634602781) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_8414022072483953011773050209369).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (205726455772006440377818607135775827053674474181634602781 - 1) / 8414022072483953011773050209369 = 24450429770654585614826620 from by norm_num]
      have h2 : (3 : ZMod 205726455772006440377818607135775827053674474181634602781) ^ 24450429770654585614826620 = ((187426773640914111703411002864066698152281976021478914024 : ℕ) : ZMod 205726455772006440377818607135775827053674474181634602781) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_260683037 : Nat.Prime 260683037 := by
  refine lucas_primality 260683037 (3 : ZMod 260683037) ?_ (fun q hq hd => ?_)
  · rw [show 260683037 - 1 = 260683036 from by norm_num]
    reduce_mod_char
  · have e : 260683037 - 1 = [2 ^ 2, 239 ^ 1, 367 ^ 1, 743 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260683037 - 1) / 2 = 130341518 from by norm_num]
      have h2 : (3 : ZMod 260683037) ^ 130341518 = ((260683036 : ℕ) : ZMod 260683037) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260683037 - 1) / 239 = 1090724 from by norm_num]
      have h2 : (3 : ZMod 260683037) ^ 1090724 = ((40826137 : ℕ) : ZMod 260683037) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260683037 - 1) / 367 = 710308 from by norm_num]
      have h2 : (3 : ZMod 260683037) ^ 710308 = ((106939137 : ℕ) : ZMod 260683037) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260683037 - 1) / 743 = 350852 from by norm_num]
      have h2 : (3 : ZMod 260683037) ^ 350852 = ((65744082 : ℕ) : ZMod 260683037) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_491103607 : Nat.Prime 491103607 := by
  refine lucas_primality 491103607 (11 : ZMod 491103607) ?_ (fun q hq hd => ?_)
  · rw [show 491103607 - 1 = 491103606 from by norm_num]
    reduce_mod_char
  · have e : 491103607 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 2153 ^ 1, 5431 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (491103607 - 1) / 2 = 245551803 from by norm_num]
      have h2 : (11 : ZMod 491103607) ^ 245551803 = ((491103606 : ℕ) : ZMod 491103607) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (491103607 - 1) / 3 = 163701202 from by norm_num]
      have h2 : (11 : ZMod 491103607) ^ 163701202 = ((216658793 : ℕ) : ZMod 491103607) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (491103607 - 1) / 7 = 70157658 from by norm_num]
      have h2 : (11 : ZMod 491103607) ^ 70157658 = ((41506854 : ℕ) : ZMod 491103607) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (491103607 - 1) / 2153 = 228102 from by norm_num]
      have h2 : (11 : ZMod 491103607) ^ 228102 = ((209611970 : ℕ) : ZMod 491103607) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (491103607 - 1) / 5431 = 90426 from by norm_num]
      have h2 : (11 : ZMod 491103607) ^ 90426 = ((169481882 : ℕ) : ZMod 491103607) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_23060668681 : Nat.Prime 23060668681 := by
  refine lucas_primality 23060668681 (11 : ZMod 23060668681) ?_ (fun q hq hd => ?_)
  · rw [show 23060668681 - 1 = 23060668680 from by norm_num]
    reduce_mod_char
  · have e : 23060668681 - 1 = [2 ^ 3, 3 ^ 3, 5 ^ 1, 7 ^ 1, 157 ^ 1, 19429 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23060668681 - 1) / 2 = 11530334340 from by norm_num]
      have h2 : (11 : ZMod 23060668681) ^ 11530334340 = ((23060668680 : ℕ) : ZMod 23060668681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23060668681 - 1) / 3 = 7686889560 from by norm_num]
      have h2 : (11 : ZMod 23060668681) ^ 7686889560 = ((4256701905 : ℕ) : ZMod 23060668681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23060668681 - 1) / 5 = 4612133736 from by norm_num]
      have h2 : (11 : ZMod 23060668681) ^ 4612133736 = ((19933142748 : ℕ) : ZMod 23060668681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23060668681 - 1) / 7 = 3294381240 from by norm_num]
      have h2 : (11 : ZMod 23060668681) ^ 3294381240 = ((787892413 : ℕ) : ZMod 23060668681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23060668681 - 1) / 157 = 146883240 from by norm_num]
      have h2 : (11 : ZMod 23060668681) ^ 146883240 = ((5952946373 : ℕ) : ZMod 23060668681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23060668681 - 1) / 19429 = 1186920 from by norm_num]
      have h2 : (11 : ZMod 23060668681) ^ 1186920 = ((470975466 : ℕ) : ZMod 23060668681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15546196279794280749075061880957 : Nat.Prime 15546196279794280749075061880957 := by
  refine lucas_primality 15546196279794280749075061880957 (3 : ZMod 15546196279794280749075061880957) ?_ (fun q hq hd => ?_)
  · rw [show 15546196279794280749075061880957 - 1 = 15546196279794280749075061880956 from by norm_num]
    reduce_mod_char
  · have e : 15546196279794280749075061880957 - 1 = [2 ^ 2, 757 ^ 1, 4019 ^ 1, 112799 ^ 1, 491103607 ^ 1, 23060668681 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15546196279794280749075061880957 - 1) / 2 = 7773098139897140374537530940478 from by norm_num]
      have h2 : (3 : ZMod 15546196279794280749075061880957) ^ 7773098139897140374537530940478 = ((15546196279794280749075061880956 : ℕ) : ZMod 15546196279794280749075061880957) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15546196279794280749075061880957 - 1) / 757 = 20536586895368930976321085708 from by norm_num]
      have h2 : (3 : ZMod 15546196279794280749075061880957) ^ 20536586895368930976321085708 = ((7064918205548446293666752768928 : ℕ) : ZMod 15546196279794280749075061880957) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15546196279794280749075061880957 - 1) / 4019 = 3868175237570112154534725524 from by norm_num]
      have h2 : (3 : ZMod 15546196279794280749075061880957) ^ 3868175237570112154534725524 = ((13060095299666113667723929354503 : ℕ) : ZMod 15546196279794280749075061880957) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15546196279794280749075061880957 - 1) / 112799 = 137822110832492138663242244 from by norm_num]
      have h2 : (3 : ZMod 15546196279794280749075061880957) ^ 137822110832492138663242244 = ((7723554909539074407153916535642 : ℕ) : ZMod 15546196279794280749075061880957) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_491103607).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15546196279794280749075061880957 - 1) / 491103607 = 31655634489759063710308 from by norm_num]
      have h2 : (3 : ZMod 15546196279794280749075061880957) ^ 31655634489759063710308 = ((14680582781988203235921391937532 : ℕ) : ZMod 15546196279794280749075061880957) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_23060668681).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15546196279794280749075061880957 - 1) / 23060668681 = 674143343146116325276 from by norm_num]
      have h2 : (3 : ZMod 15546196279794280749075061880957) ^ 674143343146116325276 = ((2433667698818389142721889649199 : ℕ) : ZMod 15546196279794280749075061880957) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_53033422111 : Nat.Prime 53033422111 := by
  refine lucas_primality 53033422111 (6 : ZMod 53033422111) ?_ (fun q hq hd => ?_)
  · rw [show 53033422111 - 1 = 53033422110 from by norm_num]
    reduce_mod_char
  · have e : 53033422111 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 2089 ^ 1, 846233 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53033422111 - 1) / 2 = 26516711055 from by norm_num]
      have h2 : (6 : ZMod 53033422111) ^ 26516711055 = ((53033422110 : ℕ) : ZMod 53033422111) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53033422111 - 1) / 3 = 17677807370 from by norm_num]
      have h2 : (6 : ZMod 53033422111) ^ 17677807370 = ((7788260037 : ℕ) : ZMod 53033422111) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53033422111 - 1) / 5 = 10606684422 from by norm_num]
      have h2 : (6 : ZMod 53033422111) ^ 10606684422 = ((42186767123 : ℕ) : ZMod 53033422111) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53033422111 - 1) / 2089 = 25386990 from by norm_num]
      have h2 : (6 : ZMod 53033422111) ^ 25386990 = ((35381295051 : ℕ) : ZMod 53033422111) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53033422111 - 1) / 846233 = 62670 from by norm_num]
      have h2 : (6 : ZMod 53033422111) ^ 62670 = ((35720939131 : ℕ) : ZMod 53033422111) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1168457387724788393 : Nat.Prime 1168457387724788393 := by
  refine lucas_primality 1168457387724788393 (5 : ZMod 1168457387724788393) ?_ (fun q hq hd => ?_)
  · rw [show 1168457387724788393 - 1 = 1168457387724788392 from by norm_num]
    reduce_mod_char
  · have e : 1168457387724788393 - 1 = [2 ^ 3, 7 ^ 1, 11 ^ 1, 47 ^ 1, 761 ^ 1, 53033422111 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1168457387724788393 - 1) / 2 = 584228693862394196 from by norm_num]
      have h2 : (5 : ZMod 1168457387724788393) ^ 584228693862394196 = ((1168457387724788392 : ℕ) : ZMod 1168457387724788393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1168457387724788393 - 1) / 7 = 166922483960684056 from by norm_num]
      have h2 : (5 : ZMod 1168457387724788393) ^ 166922483960684056 = ((945518390419309941 : ℕ) : ZMod 1168457387724788393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1168457387724788393 - 1) / 11 = 106223398884071672 from by norm_num]
      have h2 : (5 : ZMod 1168457387724788393) ^ 106223398884071672 = ((612106669793358599 : ℕ) : ZMod 1168457387724788393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1168457387724788393 - 1) / 47 = 24860795483506136 from by norm_num]
      have h2 : (5 : ZMod 1168457387724788393) ^ 24860795483506136 = ((616823545526502520 : ℕ) : ZMod 1168457387724788393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1168457387724788393 - 1) / 761 = 1535423636957672 from by norm_num]
      have h2 : (5 : ZMod 1168457387724788393) ^ 1535423636957672 = ((1049399049739562227 : ℕ) : ZMod 1168457387724788393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_53033422111).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1168457387724788393 - 1) / 53033422111 = 22032472 from by norm_num]
      have h2 : (5 : ZMod 1168457387724788393) ^ 22032472 = ((729244577900774135 : ℕ) : ZMod 1168457387724788393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1508116661 : Nat.Prime 1508116661 := by
  refine lucas_primality 1508116661 (3 : ZMod 1508116661) ?_ (fun q hq hd => ?_)
  · rw [show 1508116661 - 1 = 1508116660 from by norm_num]
    reduce_mod_char
  · have e : 1508116661 - 1 = [2 ^ 2, 5 ^ 1, 769 ^ 1, 98057 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1508116661 - 1) / 2 = 754058330 from by norm_num]
      have h2 : (3 : ZMod 1508116661) ^ 754058330 = ((1508116660 : ℕ) : ZMod 1508116661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1508116661 - 1) / 5 = 301623332 from by norm_num]
      have h2 : (3 : ZMod 1508116661) ^ 301623332 = ((585293384 : ℕ) : ZMod 1508116661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1508116661 - 1) / 769 = 1961140 from by norm_num]
      have h2 : (3 : ZMod 1508116661) ^ 1961140 = ((1381382859 : ℕ) : ZMod 1508116661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1508116661 - 1) / 98057 = 15380 from by norm_num]
      have h2 : (3 : ZMod 1508116661) ^ 15380 = ((435950135 : ℕ) : ZMod 1508116661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_400095301 : Nat.Prime 400095301 := by
  refine lucas_primality 400095301 (14 : ZMod 400095301) ?_ (fun q hq hd => ?_)
  · rw [show 400095301 - 1 = 400095300 from by norm_num]
    reduce_mod_char
  · have e : 400095301 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 2, 11 ^ 1, 31 ^ 1, 3911 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (400095301 - 1) / 2 = 200047650 from by norm_num]
      have h2 : (14 : ZMod 400095301) ^ 200047650 = ((400095300 : ℕ) : ZMod 400095301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (400095301 - 1) / 3 = 133365100 from by norm_num]
      have h2 : (14 : ZMod 400095301) ^ 133365100 = ((391954036 : ℕ) : ZMod 400095301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (400095301 - 1) / 5 = 80019060 from by norm_num]
      have h2 : (14 : ZMod 400095301) ^ 80019060 = ((345658523 : ℕ) : ZMod 400095301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (400095301 - 1) / 11 = 36372300 from by norm_num]
      have h2 : (14 : ZMod 400095301) ^ 36372300 = ((349118745 : ℕ) : ZMod 400095301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (400095301 - 1) / 31 = 12906300 from by norm_num]
      have h2 : (14 : ZMod 400095301) ^ 12906300 = ((176783254 : ℕ) : ZMod 400095301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (400095301 - 1) / 3911 = 102300 from by norm_num]
      have h2 : (14 : ZMod 400095301) ^ 102300 = ((318339387 : ℕ) : ZMod 400095301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_419181275998115173 : Nat.Prime 419181275998115173 := by
  refine lucas_primality 419181275998115173 (2 : ZMod 419181275998115173) ?_ (fun q hq hd => ?_)
  · rw [show 419181275998115173 - 1 = 419181275998115172 from by norm_num]
    reduce_mod_char
  · have e : 419181275998115173 - 1 = [2 ^ 2, 3 ^ 4, 3233653 ^ 1, 400095301 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (419181275998115173 - 1) / 2 = 209590637999057586 from by norm_num]
      have h2 : (2 : ZMod 419181275998115173) ^ 209590637999057586 = ((419181275998115172 : ℕ) : ZMod 419181275998115173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (419181275998115173 - 1) / 3 = 139727091999371724 from by norm_num]
      have h2 : (2 : ZMod 419181275998115173) ^ 139727091999371724 = ((131537094998647643 : ℕ) : ZMod 419181275998115173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (419181275998115173 - 1) / 3233653 = 129630877524 from by norm_num]
      have h2 : (2 : ZMod 419181275998115173) ^ 129630877524 = ((157832168618412877 : ℕ) : ZMod 419181275998115173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_400095301).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (419181275998115173 - 1) / 400095301 = 1047703572 from by norm_num]
      have h2 : (2 : ZMod 419181275998115173) ^ 1047703572 = ((101806863624115508 : ℕ) : ZMod 419181275998115173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_129214627 : Nat.Prime 129214627 := by
  refine lucas_primality 129214627 (2 : ZMod 129214627) ?_ (fun q hq hd => ?_)
  · rw [show 129214627 - 1 = 129214626 from by norm_num]
    reduce_mod_char
  · have e : 129214627 - 1 = [2 ^ 1, 3 ^ 1, 127 ^ 1, 151 ^ 1, 1123 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129214627 - 1) / 2 = 64607313 from by norm_num]
      have h2 : (2 : ZMod 129214627) ^ 64607313 = ((129214626 : ℕ) : ZMod 129214627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129214627 - 1) / 3 = 43071542 from by norm_num]
      have h2 : (2 : ZMod 129214627) ^ 43071542 = ((83732507 : ℕ) : ZMod 129214627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129214627 - 1) / 127 = 1017438 from by norm_num]
      have h2 : (2 : ZMod 129214627) ^ 1017438 = ((80714534 : ℕ) : ZMod 129214627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129214627 - 1) / 151 = 855726 from by norm_num]
      have h2 : (2 : ZMod 129214627) ^ 855726 = ((51953651 : ℕ) : ZMod 129214627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129214627 - 1) / 1123 = 115062 from by norm_num]
      have h2 : (2 : ZMod 129214627) ^ 115062 = ((114677502 : ℕ) : ZMod 129214627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_516858509 : Nat.Prime 516858509 := by
  refine lucas_primality 516858509 (2 : ZMod 516858509) ?_ (fun q hq hd => ?_)
  · rw [show 516858509 - 1 = 516858508 from by norm_num]
    reduce_mod_char
  · have e : 516858509 - 1 = [2 ^ 2, 129214627 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (516858509 - 1) / 2 = 258429254 from by norm_num]
      have h2 : (2 : ZMod 516858509) ^ 258429254 = ((516858508 : ℕ) : ZMod 516858509) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_129214627).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (516858509 - 1) / 129214627 = 4 from by norm_num]
      have h2 : (2 : ZMod 516858509) ^ 4 = ((16 : ℕ) : ZMod 516858509) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_93308601461 : Nat.Prime 93308601461 := by
  refine lucas_primality 93308601461 (2 : ZMod 93308601461) ?_ (fun q hq hd => ?_)
  · rw [show 93308601461 - 1 = 93308601460 from by norm_num]
    reduce_mod_char
  · have e : 93308601461 - 1 = [2 ^ 2, 5 ^ 1, 73 ^ 1, 211 ^ 1, 302891 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93308601461 - 1) / 2 = 46654300730 from by norm_num]
      have h2 : (2 : ZMod 93308601461) ^ 46654300730 = ((93308601460 : ℕ) : ZMod 93308601461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93308601461 - 1) / 5 = 18661720292 from by norm_num]
      have h2 : (2 : ZMod 93308601461) ^ 18661720292 = ((85044499352 : ℕ) : ZMod 93308601461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93308601461 - 1) / 73 = 1278200020 from by norm_num]
      have h2 : (2 : ZMod 93308601461) ^ 1278200020 = ((89970302367 : ℕ) : ZMod 93308601461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93308601461 - 1) / 211 = 442220860 from by norm_num]
      have h2 : (2 : ZMod 93308601461) ^ 442220860 = ((77468206686 : ℕ) : ZMod 93308601461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93308601461 - 1) / 302891 = 308060 from by norm_num]
      have h2 : (2 : ZMod 93308601461) ^ 308060 = ((68252116026 : ℕ) : ZMod 93308601461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_746468811689 : Nat.Prime 746468811689 := by
  refine lucas_primality 746468811689 (3 : ZMod 746468811689) ?_ (fun q hq hd => ?_)
  · rw [show 746468811689 - 1 = 746468811688 from by norm_num]
    reduce_mod_char
  · have e : 746468811689 - 1 = [2 ^ 3, 93308601461 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (746468811689 - 1) / 2 = 373234405844 from by norm_num]
      have h2 : (3 : ZMod 746468811689) ^ 373234405844 = ((746468811688 : ℕ) : ZMod 746468811689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_93308601461).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (746468811689 - 1) / 93308601461 = 8 from by norm_num]
      have h2 : (3 : ZMod 746468811689) ^ 8 = ((6561 : ℕ) : ZMod 746468811689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_732359058210454523 : Nat.Prime 732359058210454523 := by
  refine lucas_primality 732359058210454523 (2 : ZMod 732359058210454523) ?_ (fun q hq hd => ?_)
  · rw [show 732359058210454523 - 1 = 732359058210454522 from by norm_num]
    reduce_mod_char
  · have e : 732359058210454523 - 1 = [2 ^ 1, 490549 ^ 1, 746468811689 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (732359058210454523 - 1) / 2 = 366179529105227261 from by norm_num]
      have h2 : (2 : ZMod 732359058210454523) ^ 366179529105227261 = ((732359058210454522 : ℕ) : ZMod 732359058210454523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (732359058210454523 - 1) / 490549 = 1492937623378 from by norm_num]
      have h2 : (2 : ZMod 732359058210454523) ^ 1492937623378 = ((189303899225967459 : ℕ) : ZMod 732359058210454523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_746468811689).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (732359058210454523 - 1) / 746468811689 = 981098 from by norm_num]
      have h2 : (2 : ZMod 732359058210454523) ^ 981098 = ((116573094211642595 : ℕ) : ZMod 732359058210454523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_40123757153205771694829137943 : Nat.Prime 40123757153205771694829137943 := by
  refine lucas_primality 40123757153205771694829137943 (5 : ZMod 40123757153205771694829137943) ?_ (fun q hq hd => ?_)
  · rw [show 40123757153205771694829137943 - 1 = 40123757153205771694829137942 from by norm_num]
    reduce_mod_char
  · have e : 40123757153205771694829137943 - 1 = [2 ^ 1, 53 ^ 1, 516858509 ^ 1, 732359058210454523 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40123757153205771694829137943 - 1) / 2 = 20061878576602885847414568971 from by norm_num]
      have h2 : (5 : ZMod 40123757153205771694829137943) ^ 20061878576602885847414568971 = ((40123757153205771694829137942 : ℕ) : ZMod 40123757153205771694829137943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40123757153205771694829137943 - 1) / 53 = 757052021758599465940172414 from by norm_num]
      have h2 : (5 : ZMod 40123757153205771694829137943) ^ 757052021758599465940172414 = ((21670063492145819801115458034 : ℕ) : ZMod 40123757153205771694829137943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_516858509).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40123757153205771694829137943 - 1) / 516858509 = 77630060170308179438 from by norm_num]
      have h2 : (5 : ZMod 40123757153205771694829137943) ^ 77630060170308179438 = ((8070036105138230064566709463 : ℕ) : ZMod 40123757153205771694829137943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_732359058210454523).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40123757153205771694829137943 - 1) / 732359058210454523 = 54787001954 from by norm_num]
      have h2 : (5 : ZMod 40123757153205771694829137943) ^ 54787001954 = ((27146032502646452620680053029 : ℕ) : ZMod 40123757153205771694829137943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_50902080564527017360173061387390051814344996542268977221 : Nat.Prime 50902080564527017360173061387390051814344996542268977221 := by
  refine lucas_primality 50902080564527017360173061387390051814344996542268977221 (3 : ZMod 50902080564527017360173061387390051814344996542268977221) ?_ (fun q hq hd => ?_)
  · rw [show 50902080564527017360173061387390051814344996542268977221 - 1 = 50902080564527017360173061387390051814344996542268977220 from by norm_num]
    reduce_mod_char
  · have e : 50902080564527017360173061387390051814344996542268977221 - 1 = [2 ^ 2, 5 ^ 1, 47 ^ 1, 787 ^ 1, 4091 ^ 1, 419181275998115173 ^ 1, 40123757153205771694829137943 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50902080564527017360173061387390051814344996542268977221 - 1) / 2 = 25451040282263508680086530693695025907172498271134488610 from by norm_num]
      have h2 : (3 : ZMod 50902080564527017360173061387390051814344996542268977221) ^ 25451040282263508680086530693695025907172498271134488610 = ((50902080564527017360173061387390051814344996542268977220 : ℕ) : ZMod 50902080564527017360173061387390051814344996542268977221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50902080564527017360173061387390051814344996542268977221 - 1) / 5 = 10180416112905403472034612277478010362868999308453795444 from by norm_num]
      have h2 : (3 : ZMod 50902080564527017360173061387390051814344996542268977221) ^ 10180416112905403472034612277478010362868999308453795444 = ((33701914296338716271436936896270015709107157080886733836 : ℕ) : ZMod 50902080564527017360173061387390051814344996542268977221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50902080564527017360173061387390051814344996542268977221 - 1) / 47 = 1083022990734617390641980029518937272645638224303595260 from by norm_num]
      have h2 : (3 : ZMod 50902080564527017360173061387390051814344996542268977221) ^ 1083022990734617390641980029518937272645638224303595260 = ((15089110556480690787651047065119268169943376769119292829 : ℕ) : ZMod 50902080564527017360173061387390051814344996542268977221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50902080564527017360173061387390051814344996542268977221 - 1) / 787 = 64678628417442207573282161864536279306664544526390060 from by norm_num]
      have h2 : (3 : ZMod 50902080564527017360173061387390051814344996542268977221) ^ 64678628417442207573282161864536279306664544526390060 = ((2496554416573271081324027034135809308578268733625592344 : ℕ) : ZMod 50902080564527017360173061387390051814344996542268977221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50902080564527017360173061387390051814344996542268977221 - 1) / 4091 = 12442454305677589186060391441552200394608896734849420 from by norm_num]
      have h2 : (3 : ZMod 50902080564527017360173061387390051814344996542268977221) ^ 12442454305677589186060391441552200394608896734849420 = ((17831652740598119129866027249827501166220043349302420158 : ℕ) : ZMod 50902080564527017360173061387390051814344996542268977221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_419181275998115173).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50902080564527017360173061387390051814344996542268977221 - 1) / 419181275998115173 = 121432142796272932623983262339630161140 from by norm_num]
      have h2 : (3 : ZMod 50902080564527017360173061387390051814344996542268977221) ^ 121432142796272932623983262339630161140 = ((22616020606545450498021671671806445138879771921807876230 : ℕ) : ZMod 50902080564527017360173061387390051814344996542268977221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_40123757153205771694829137943).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50902080564527017360173061387390051814344996542268977221 - 1) / 40123757153205771694829137943 = 1268626972548110164211816540 from by norm_num]
      have h2 : (3 : ZMod 50902080564527017360173061387390051814344996542268977221) ^ 1268626972548110164211816540 = ((38018204704410092239920033829285415580248887697912683646 : ℕ) : ZMod 50902080564527017360173061387390051814344996542268977221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1131019499249 : Nat.Prime 1131019499249 := by
  refine lucas_primality 1131019499249 (3 : ZMod 1131019499249) ?_ (fun q hq hd => ?_)
  · rw [show 1131019499249 - 1 = 1131019499248 from by norm_num]
    reduce_mod_char
  · have e : 1131019499249 - 1 = [2 ^ 4, 797 ^ 1, 4339 ^ 1, 20441 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1131019499249 - 1) / 2 = 565509749624 from by norm_num]
      have h2 : (3 : ZMod 1131019499249) ^ 565509749624 = ((1131019499248 : ℕ) : ZMod 1131019499249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1131019499249 - 1) / 797 = 1419095984 from by norm_num]
      have h2 : (3 : ZMod 1131019499249) ^ 1419095984 = ((63394046407 : ℕ) : ZMod 1131019499249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1131019499249 - 1) / 4339 = 260663632 from by norm_num]
      have h2 : (3 : ZMod 1131019499249) ^ 260663632 = ((582832619601 : ℕ) : ZMod 1131019499249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1131019499249 - 1) / 20441 = 55330928 from by norm_num]
      have h2 : (3 : ZMod 1131019499249) ^ 55330928 = ((482335152124 : ℕ) : ZMod 1131019499249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_260999287268899 : Nat.Prime 260999287268899 := by
  refine lucas_primality 260999287268899 (2 : ZMod 260999287268899) ?_ (fun q hq hd => ?_)
  · rw [show 260999287268899 - 1 = 260999287268898 from by norm_num]
    reduce_mod_char
  · have e : 260999287268899 - 1 = [2 ^ 1, 3 ^ 1, 101 ^ 1, 6481 ^ 1, 6971 ^ 1, 9533 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260999287268899 - 1) / 2 = 130499643634449 from by norm_num]
      have h2 : (2 : ZMod 260999287268899) ^ 130499643634449 = ((260999287268898 : ℕ) : ZMod 260999287268899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260999287268899 - 1) / 3 = 86999762422966 from by norm_num]
      have h2 : (2 : ZMod 260999287268899) ^ 86999762422966 = ((243234575120321 : ℕ) : ZMod 260999287268899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260999287268899 - 1) / 101 = 2584151359098 from by norm_num]
      have h2 : (2 : ZMod 260999287268899) ^ 2584151359098 = ((97679537534219 : ℕ) : ZMod 260999287268899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260999287268899 - 1) / 6481 = 40271453058 from by norm_num]
      have h2 : (2 : ZMod 260999287268899) ^ 40271453058 = ((46371088575277 : ℕ) : ZMod 260999287268899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260999287268899 - 1) / 6971 = 37440724038 from by norm_num]
      have h2 : (2 : ZMod 260999287268899) ^ 37440724038 = ((3478039780856 : ℕ) : ZMod 260999287268899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260999287268899 - 1) / 9533 = 27378504906 from by norm_num]
      have h2 : (2 : ZMod 260999287268899) ^ 27378504906 = ((233517078679148 : ℕ) : ZMod 260999287268899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1043997149075597 : Nat.Prime 1043997149075597 := by
  refine lucas_primality 1043997149075597 (2 : ZMod 1043997149075597) ?_ (fun q hq hd => ?_)
  · rw [show 1043997149075597 - 1 = 1043997149075596 from by norm_num]
    reduce_mod_char
  · have e : 1043997149075597 - 1 = [2 ^ 2, 260999287268899 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1043997149075597 - 1) / 2 = 521998574537798 from by norm_num]
      have h2 : (2 : ZMod 1043997149075597) ^ 521998574537798 = ((1043997149075596 : ℕ) : ZMod 1043997149075597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_260999287268899).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1043997149075597 - 1) / 260999287268899 = 4 from by norm_num]
      have h2 : (2 : ZMod 1043997149075597) ^ 4 = ((16 : ℕ) : ZMod 1043997149075597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_924509587369596772157 : Nat.Prime 924509587369596772157 := by
  refine lucas_primality 924509587369596772157 (3 : ZMod 924509587369596772157) ?_ (fun q hq hd => ?_)
  · rw [show 924509587369596772157 - 1 = 924509587369596772156 from by norm_num]
    reduce_mod_char
  · have e : 924509587369596772157 - 1 = [2 ^ 2, 269 ^ 1, 823 ^ 1, 1043997149075597 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (924509587369596772157 - 1) / 2 = 462254793684798386078 from by norm_num]
      have h2 : (3 : ZMod 924509587369596772157) ^ 462254793684798386078 = ((924509587369596772156 : ℕ) : ZMod 924509587369596772157) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (924509587369596772157 - 1) / 269 = 3436838614756865324 from by norm_num]
      have h2 : (3 : ZMod 924509587369596772157) ^ 3436838614756865324 = ((125215547574135532849 : ℕ) : ZMod 924509587369596772157) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (924509587369596772157 - 1) / 823 = 1123340932405342372 from by norm_num]
      have h2 : (3 : ZMod 924509587369596772157) ^ 1123340932405342372 = ((708240922596123853041 : ℕ) : ZMod 924509587369596772157) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1043997149075597).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (924509587369596772157 - 1) / 1043997149075597 = 885548 from by norm_num]
      have h2 : (3 : ZMod 924509587369596772157) ^ 885548 = ((111596882525341248439 : ℕ) : ZMod 924509587369596772157) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_50308897 : Nat.Prime 50308897 := by
  refine lucas_primality 50308897 (5 : ZMod 50308897) ?_ (fun q hq hd => ?_)
  · rw [show 50308897 - 1 = 50308896 from by norm_num]
    reduce_mod_char
  · have e : 50308897 - 1 = [2 ^ 5, 3 ^ 1, 11 ^ 2, 61 ^ 1, 71 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50308897 - 1) / 2 = 25154448 from by norm_num]
      have h2 : (5 : ZMod 50308897) ^ 25154448 = ((50308896 : ℕ) : ZMod 50308897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50308897 - 1) / 3 = 16769632 from by norm_num]
      have h2 : (5 : ZMod 50308897) ^ 16769632 = ((6066922 : ℕ) : ZMod 50308897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50308897 - 1) / 11 = 4573536 from by norm_num]
      have h2 : (5 : ZMod 50308897) ^ 4573536 = ((38951474 : ℕ) : ZMod 50308897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50308897 - 1) / 61 = 824736 from by norm_num]
      have h2 : (5 : ZMod 50308897) ^ 824736 = ((41414681 : ℕ) : ZMod 50308897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50308897 - 1) / 71 = 708576 from by norm_num]
      have h2 : (5 : ZMod 50308897) ^ 708576 = ((20407496 : ℕ) : ZMod 50308897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_14930234248811251 : Nat.Prime 14930234248811251 := by
  refine lucas_primality 14930234248811251 (3 : ZMod 14930234248811251) ?_ (fun q hq hd => ?_)
  · rw [show 14930234248811251 - 1 = 14930234248811250 from by norm_num]
    reduce_mod_char
  · have e : 14930234248811251 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 4, 79139 ^ 1, 50308897 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14930234248811251 - 1) / 2 = 7465117124405625 from by norm_num]
      have h2 : (3 : ZMod 14930234248811251) ^ 7465117124405625 = ((14930234248811250 : ℕ) : ZMod 14930234248811251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14930234248811251 - 1) / 3 = 4976744749603750 from by norm_num]
      have h2 : (3 : ZMod 14930234248811251) ^ 4976744749603750 = ((12480465119499797 : ℕ) : ZMod 14930234248811251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14930234248811251 - 1) / 5 = 2986046849762250 from by norm_num]
      have h2 : (3 : ZMod 14930234248811251) ^ 2986046849762250 = ((13818760912227847 : ℕ) : ZMod 14930234248811251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14930234248811251 - 1) / 79139 = 188658363750 from by norm_num]
      have h2 : (3 : ZMod 14930234248811251) ^ 188658363750 = ((12262094206359227 : ℕ) : ZMod 14930234248811251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_50308897).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14930234248811251 - 1) / 50308897 = 296771250 from by norm_num]
      have h2 : (3 : ZMod 14930234248811251) ^ 296771250 = ((2073314846782590 : ℕ) : ZMod 14930234248811251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_12624459932825972330038421 : Nat.Prime 12624459932825972330038421 := by
  refine lucas_primality 12624459932825972330038421 (3 : ZMod 12624459932825972330038421) ?_ (fun q hq hd => ?_)
  · rw [show 12624459932825972330038421 - 1 = 12624459932825972330038420 from by norm_num]
    reduce_mod_char
  · have e : 12624459932825972330038421 - 1 = [2 ^ 2, 5 ^ 1, 13 ^ 1, 829 ^ 1, 3923 ^ 1, 14930234248811251 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12624459932825972330038421 - 1) / 2 = 6312229966412986165019210 from by norm_num]
      have h2 : (3 : ZMod 12624459932825972330038421) ^ 6312229966412986165019210 = ((12624459932825972330038420 : ℕ) : ZMod 12624459932825972330038421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12624459932825972330038421 - 1) / 5 = 2524891986565194466007684 from by norm_num]
      have h2 : (3 : ZMod 12624459932825972330038421) ^ 2524891986565194466007684 = ((10582742114138081712934401 : ℕ) : ZMod 12624459932825972330038421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12624459932825972330038421 - 1) / 13 = 971112302525074794618340 from by norm_num]
      have h2 : (3 : ZMod 12624459932825972330038421) ^ 971112302525074794618340 = ((3238683424951563507080038 : ℕ) : ZMod 12624459932825972330038421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12624459932825972330038421 - 1) / 829 = 15228540329102499794980 from by norm_num]
      have h2 : (3 : ZMod 12624459932825972330038421) ^ 15228540329102499794980 = ((11073279632579322817114186 : ℕ) : ZMod 12624459932825972330038421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12624459932825972330038421 - 1) / 3923 = 3218062689988777040540 from by norm_num]
      have h2 : (3 : ZMod 12624459932825972330038421) ^ 3218062689988777040540 = ((6732327032166048839082156 : ℕ) : ZMod 12624459932825972330038421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_14930234248811251).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12624459932825972330038421 - 1) / 14930234248811251 = 845563420 from by norm_num]
      have h2 : (3 : ZMod 12624459932825972330038421) ^ 845563420 = ((12124053422507534678633672 : ℕ) : ZMod 12624459932825972330038421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3972662123 : Nat.Prime 3972662123 := by
  refine lucas_primality 3972662123 (2 : ZMod 3972662123) ?_ (fun q hq hd => ?_)
  · rw [show 3972662123 - 1 = 3972662122 from by norm_num]
    reduce_mod_char
  · have e : 3972662123 - 1 = [2 ^ 1, 11 ^ 1, 13 ^ 1, 47 ^ 1, 295541 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3972662123 - 1) / 2 = 1986331061 from by norm_num]
      have h2 : (2 : ZMod 3972662123) ^ 1986331061 = ((3972662122 : ℕ) : ZMod 3972662123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3972662123 - 1) / 11 = 361151102 from by norm_num]
      have h2 : (2 : ZMod 3972662123) ^ 361151102 = ((196786385 : ℕ) : ZMod 3972662123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3972662123 - 1) / 13 = 305589394 from by norm_num]
      have h2 : (2 : ZMod 3972662123) ^ 305589394 = ((1897096572 : ℕ) : ZMod 3972662123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3972662123 - 1) / 47 = 84524726 from by norm_num]
      have h2 : (2 : ZMod 3972662123) ^ 84524726 = ((3903774249 : ℕ) : ZMod 3972662123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3972662123 - 1) / 295541 = 13442 from by norm_num]
      have h2 : (2 : ZMod 3972662123) ^ 13442 = ((2020218038 : ℕ) : ZMod 3972662123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1122047772459197542365557 : Nat.Prime 1122047772459197542365557 := by
  refine lucas_primality 1122047772459197542365557 (3 : ZMod 1122047772459197542365557) ?_ (fun q hq hd => ?_)
  · rw [show 1122047772459197542365557 - 1 = 1122047772459197542365556 from by norm_num]
    reduce_mod_char
  · have e : 1122047772459197542365557 - 1 = [2 ^ 2, 853 ^ 1, 177427 ^ 1, 466553 ^ 1, 3972662123 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1122047772459197542365557 - 1) / 2 = 561023886229598771182778 from by norm_num]
      have h2 : (3 : ZMod 1122047772459197542365557) ^ 561023886229598771182778 = ((1122047772459197542365556 : ℕ) : ZMod 1122047772459197542365557) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1122047772459197542365557 - 1) / 853 = 1315413566775143660452 from by norm_num]
      have h2 : (3 : ZMod 1122047772459197542365557) ^ 1315413566775143660452 = ((196524034662267561923914 : ℕ) : ZMod 1122047772459197542365557) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1122047772459197542365557 - 1) / 177427 = 6323996756182528828 from by norm_num]
      have h2 : (3 : ZMod 1122047772459197542365557) ^ 6323996756182528828 = ((1032099340956725969881447 : ℕ) : ZMod 1122047772459197542365557) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1122047772459197542365557 - 1) / 466553 = 2404973866761541652 from by norm_num]
      have h2 : (3 : ZMod 1122047772459197542365557) ^ 2404973866761541652 = ((266822621859192388435352 : ℕ) : ZMod 1122047772459197542365557) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3972662123).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1122047772459197542365557 - 1) / 3972662123 = 282442286234972 from by norm_num]
      have h2 : (3 : ZMod 1122047772459197542365557) ^ 282442286234972 = ((217526008004108277204789 : ℕ) : ZMod 1122047772459197542365557) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_66549023117 : Nat.Prime 66549023117 := by
  refine lucas_primality 66549023117 (3 : ZMod 66549023117) ?_ (fun q hq hd => ?_)
  · rw [show 66549023117 - 1 = 66549023116 from by norm_num]
    reduce_mod_char
  · have e : 66549023117 - 1 = [2 ^ 2, 19 ^ 1, 1733 ^ 1, 505277 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (66549023117 - 1) / 2 = 33274511558 from by norm_num]
      have h2 : (3 : ZMod 66549023117) ^ 33274511558 = ((66549023116 : ℕ) : ZMod 66549023117) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (66549023117 - 1) / 19 = 3502580164 from by norm_num]
      have h2 : (3 : ZMod 66549023117) ^ 3502580164 = ((26115434410 : ℕ) : ZMod 66549023117) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (66549023117 - 1) / 1733 = 38401052 from by norm_num]
      have h2 : (3 : ZMod 66549023117) ^ 38401052 = ((32577468983 : ℕ) : ZMod 66549023117) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (66549023117 - 1) / 505277 = 131708 from by norm_num]
      have h2 : (3 : ZMod 66549023117) ^ 131708 = ((64822051794 : ℕ) : ZMod 66549023117) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_25954119015631 : Nat.Prime 25954119015631 := by
  refine lucas_primality 25954119015631 (7 : ZMod 25954119015631) ?_ (fun q hq hd => ?_)
  · rw [show 25954119015631 - 1 = 25954119015630 from by norm_num]
    reduce_mod_char
  · have e : 25954119015631 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 13 ^ 1, 66549023117 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25954119015631 - 1) / 2 = 12977059507815 from by norm_num]
      have h2 : (7 : ZMod 25954119015631) ^ 12977059507815 = ((25954119015630 : ℕ) : ZMod 25954119015631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25954119015631 - 1) / 3 = 8651373005210 from by norm_num]
      have h2 : (7 : ZMod 25954119015631) ^ 8651373005210 = ((7386621009508 : ℕ) : ZMod 25954119015631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25954119015631 - 1) / 5 = 5190823803126 from by norm_num]
      have h2 : (7 : ZMod 25954119015631) ^ 5190823803126 = ((5241423838035 : ℕ) : ZMod 25954119015631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25954119015631 - 1) / 13 = 1996470693510 from by norm_num]
      have h2 : (7 : ZMod 25954119015631) ^ 1996470693510 = ((22752645868936 : ℕ) : ZMod 25954119015631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_66549023117).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25954119015631 - 1) / 66549023117 = 390 from by norm_num]
      have h2 : (7 : ZMod 25954119015631) ^ 390 = ((23738954609364 : ℕ) : ZMod 25954119015631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_51158163991710264101 : Nat.Prime 51158163991710264101 := by
  refine lucas_primality 51158163991710264101 (3 : ZMod 51158163991710264101) ?_ (fun q hq hd => ?_)
  · rw [show 51158163991710264101 - 1 = 51158163991710264100 from by norm_num]
    reduce_mod_char
  · have e : 51158163991710264101 - 1 = [2 ^ 2, 5 ^ 2, 23 ^ 1, 857 ^ 1, 25954119015631 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51158163991710264101 - 1) / 2 = 25579081995855132050 from by norm_num]
      have h2 : (3 : ZMod 51158163991710264101) ^ 25579081995855132050 = ((51158163991710264100 : ℕ) : ZMod 51158163991710264101) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51158163991710264101 - 1) / 5 = 10231632798342052820 from by norm_num]
      have h2 : (3 : ZMod 51158163991710264101) ^ 10231632798342052820 = ((39497516480820513551 : ℕ) : ZMod 51158163991710264101) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51158163991710264101 - 1) / 23 = 2224267999639576700 from by norm_num]
      have h2 : (3 : ZMod 51158163991710264101) ^ 2224267999639576700 = ((46800312978519240638 : ℕ) : ZMod 51158163991710264101) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51158163991710264101 - 1) / 857 = 59694473735951300 from by norm_num]
      have h2 : (3 : ZMod 51158163991710264101) ^ 59694473735951300 = ((39398777166422917288 : ℕ) : ZMod 51158163991710264101) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_25954119015631).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51158163991710264101 - 1) / 25954119015631 = 1971100 from by norm_num]
      have h2 : (3 : ZMod 51158163991710264101) ^ 1971100 = ((28472831111542076302 : ℕ) : ZMod 51158163991710264101) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_82488053 : Nat.Prime 82488053 := by
  refine lucas_primality 82488053 (3 : ZMod 82488053) ?_ (fun q hq hd => ?_)
  · rw [show 82488053 - 1 = 82488052 from by norm_num]
    reduce_mod_char
  · have e : 82488053 - 1 = [2 ^ 2, 859 ^ 1, 24007 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82488053 - 1) / 2 = 41244026 from by norm_num]
      have h2 : (3 : ZMod 82488053) ^ 41244026 = ((82488052 : ℕ) : ZMod 82488053) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82488053 - 1) / 859 = 96028 from by norm_num]
      have h2 : (3 : ZMod 82488053) ^ 96028 = ((59890561 : ℕ) : ZMod 82488053) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82488053 - 1) / 24007 = 3436 from by norm_num]
      have h2 : (3 : ZMod 82488053) ^ 3436 = ((71405750 : ℕ) : ZMod 82488053) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_90275681 : Nat.Prime 90275681 := by
  refine lucas_primality 90275681 (3 : ZMod 90275681) ?_ (fun q hq hd => ?_)
  · rw [show 90275681 - 1 = 90275680 from by norm_num]
    reduce_mod_char
  · have e : 90275681 - 1 = [2 ^ 5, 5 ^ 1, 11 ^ 2, 4663 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (90275681 - 1) / 2 = 45137840 from by norm_num]
      have h2 : (3 : ZMod 90275681) ^ 45137840 = ((90275680 : ℕ) : ZMod 90275681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (90275681 - 1) / 5 = 18055136 from by norm_num]
      have h2 : (3 : ZMod 90275681) ^ 18055136 = ((57075402 : ℕ) : ZMod 90275681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (90275681 - 1) / 11 = 8206880 from by norm_num]
      have h2 : (3 : ZMod 90275681) ^ 8206880 = ((81858307 : ℕ) : ZMod 90275681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (90275681 - 1) / 4663 = 19360 from by norm_num]
      have h2 : (3 : ZMod 90275681) ^ 19360 = ((5551584 : ℕ) : ZMod 90275681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_41734812223623741861146169997 : Nat.Prime 41734812223623741861146169997 := by
  refine lucas_primality 41734812223623741861146169997 (5 : ZMod 41734812223623741861146169997) ?_ (fun q hq hd => ?_)
  · rw [show 41734812223623741861146169997 - 1 = 41734812223623741861146169996 from by norm_num]
    reduce_mod_char
  · have e : 41734812223623741861146169997 - 1 = [2 ^ 2, 3 ^ 4, 53 ^ 1, 563 ^ 1, 863 ^ 1, 5711 ^ 1, 9702317 ^ 1, 90275681 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41734812223623741861146169997 - 1) / 2 = 20867406111811870930573084998 from by norm_num]
      have h2 : (5 : ZMod 41734812223623741861146169997) ^ 20867406111811870930573084998 = ((41734812223623741861146169996 : ℕ) : ZMod 41734812223623741861146169997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41734812223623741861146169997 - 1) / 3 = 13911604074541247287048723332 from by norm_num]
      have h2 : (5 : ZMod 41734812223623741861146169997) ^ 13911604074541247287048723332 = ((15342316450042122128278314905 : ℕ) : ZMod 41734812223623741861146169997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41734812223623741861146169997 - 1) / 53 = 787449287238183808700871132 from by norm_num]
      have h2 : (5 : ZMod 41734812223623741861146169997) ^ 787449287238183808700871132 = ((18418403678065047041857748363 : ℕ) : ZMod 41734812223623741861146169997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41734812223623741861146169997 - 1) / 563 = 74129328994003093891911492 from by norm_num]
      have h2 : (5 : ZMod 41734812223623741861146169997) ^ 74129328994003093891911492 = ((21286357551122510729357319815 : ℕ) : ZMod 41734812223623741861146169997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41734812223623741861146169997 - 1) / 863 = 48360153213932493465986292 from by norm_num]
      have h2 : (5 : ZMod 41734812223623741861146169997) ^ 48360153213932493465986292 = ((2261837885652389776319940379 : ℕ) : ZMod 41734812223623741861146169997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41734812223623741861146169997 - 1) / 5711 = 7307794120753588138880436 from by norm_num]
      have h2 : (5 : ZMod 41734812223623741861146169997) ^ 7307794120753588138880436 = ((4868266931778993022788420803 : ℕ) : ZMod 41734812223623741861146169997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41734812223623741861146169997 - 1) / 9702317 = 4301530471909312163388 from by norm_num]
      have h2 : (5 : ZMod 41734812223623741861146169997) ^ 4301530471909312163388 = ((30460552940601958073116462625 : ℕ) : ZMod 41734812223623741861146169997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_90275681).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41734812223623741861146169997 - 1) / 90275681 = 462304042033465711116 from by norm_num]
      have h2 : (5 : ZMod 41734812223623741861146169997) ^ 462304042033465711116 = ((30935151693488111400284862303 : ℕ) : ZMod 41734812223623741861146169997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8045864609 : Nat.Prime 8045864609 := by
  refine lucas_primality 8045864609 (3 : ZMod 8045864609) ?_ (fun q hq hd => ?_)
  · rw [show 8045864609 - 1 = 8045864608 from by norm_num]
    reduce_mod_char
  · have e : 8045864609 - 1 = [2 ^ 5, 877 ^ 1, 286697 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8045864609 - 1) / 2 = 4022932304 from by norm_num]
      have h2 : (3 : ZMod 8045864609) ^ 4022932304 = ((8045864608 : ℕ) : ZMod 8045864609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8045864609 - 1) / 877 = 9174304 from by norm_num]
      have h2 : (3 : ZMod 8045864609) ^ 9174304 = ((2653508964 : ℕ) : ZMod 8045864609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8045864609 - 1) / 286697 = 28064 from by norm_num]
      have h2 : (3 : ZMod 8045864609) ^ 28064 = ((507198884 : ℕ) : ZMod 8045864609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_94177931835255001 : Nat.Prime 94177931835255001 := by
  refine lucas_primality 94177931835255001 (7 : ZMod 94177931835255001) ?_ (fun q hq hd => ?_)
  · rw [show 94177931835255001 - 1 = 94177931835255000 from by norm_num]
    reduce_mod_char
  · have e : 94177931835255001 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 4, 43 ^ 1, 313 ^ 1, 877 ^ 1, 531919 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94177931835255001 - 1) / 2 = 47088965917627500 from by norm_num]
      have h2 : (7 : ZMod 94177931835255001) ^ 47088965917627500 = ((94177931835255000 : ℕ) : ZMod 94177931835255001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94177931835255001 - 1) / 3 = 31392643945085000 from by norm_num]
      have h2 : (7 : ZMod 94177931835255001) ^ 31392643945085000 = ((8679593984387167 : ℕ) : ZMod 94177931835255001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94177931835255001 - 1) / 5 = 18835586367051000 from by norm_num]
      have h2 : (7 : ZMod 94177931835255001) ^ 18835586367051000 = ((91498928941800839 : ℕ) : ZMod 94177931835255001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94177931835255001 - 1) / 43 = 2190184461285000 from by norm_num]
      have h2 : (7 : ZMod 94177931835255001) ^ 2190184461285000 = ((48674638096961332 : ℕ) : ZMod 94177931835255001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94177931835255001 - 1) / 313 = 300887961135000 from by norm_num]
      have h2 : (7 : ZMod 94177931835255001) ^ 300887961135000 = ((50649608723552250 : ℕ) : ZMod 94177931835255001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94177931835255001 - 1) / 877 = 107386467315000 from by norm_num]
      have h2 : (7 : ZMod 94177931835255001) ^ 107386467315000 = ((58778015219149630 : ℕ) : ZMod 94177931835255001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94177931835255001 - 1) / 531919 = 177053145000 from by norm_num]
      have h2 : (7 : ZMod 94177931835255001) ^ 177053145000 = ((53015484365851864 : ℕ) : ZMod 94177931835255001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9642835106981 : Nat.Prime 9642835106981 := by
  refine lucas_primality 9642835106981 (3 : ZMod 9642835106981) ?_ (fun q hq hd => ?_)
  · rw [show 9642835106981 - 1 = 9642835106980 from by norm_num]
    reduce_mod_char
  · have e : 9642835106981 - 1 = [2 ^ 2, 5 ^ 1, 349 ^ 1, 677 ^ 1, 883 ^ 1, 2311 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9642835106981 - 1) / 2 = 4821417553490 from by norm_num]
      have h2 : (3 : ZMod 9642835106981) ^ 4821417553490 = ((9642835106980 : ℕ) : ZMod 9642835106981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9642835106981 - 1) / 5 = 1928567021396 from by norm_num]
      have h2 : (3 : ZMod 9642835106981) ^ 1928567021396 = ((2904043881456 : ℕ) : ZMod 9642835106981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9642835106981 - 1) / 349 = 27629900020 from by norm_num]
      have h2 : (3 : ZMod 9642835106981) ^ 27629900020 = ((9298345324077 : ℕ) : ZMod 9642835106981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9642835106981 - 1) / 677 = 14243478740 from by norm_num]
      have h2 : (3 : ZMod 9642835106981) ^ 14243478740 = ((5512471956672 : ℕ) : ZMod 9642835106981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9642835106981 - 1) / 883 = 10920538060 from by norm_num]
      have h2 : (3 : ZMod 9642835106981) ^ 10920538060 = ((5370605763591 : ℕ) : ZMod 9642835106981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9642835106981 - 1) / 2311 = 4172581180 from by norm_num]
      have h2 : (3 : ZMod 9642835106981) ^ 4172581180 = ((4819071839432 : ℕ) : ZMod 9642835106981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1982764321 : Nat.Prime 1982764321 := by
  refine lucas_primality 1982764321 (11 : ZMod 1982764321) ?_ (fun q hq hd => ?_)
  · rw [show 1982764321 - 1 = 1982764320 from by norm_num]
    reduce_mod_char
  · have e : 1982764321 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 887 ^ 1, 4657 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1982764321 - 1) / 2 = 991382160 from by norm_num]
      have h2 : (11 : ZMod 1982764321) ^ 991382160 = ((1982764320 : ℕ) : ZMod 1982764321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1982764321 - 1) / 3 = 660921440 from by norm_num]
      have h2 : (11 : ZMod 1982764321) ^ 660921440 = ((1574851985 : ℕ) : ZMod 1982764321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1982764321 - 1) / 5 = 396552864 from by norm_num]
      have h2 : (11 : ZMod 1982764321) ^ 396552864 = ((1797398244 : ℕ) : ZMod 1982764321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1982764321 - 1) / 887 = 2235360 from by norm_num]
      have h2 : (11 : ZMod 1982764321) ^ 2235360 = ((431804463 : ℕ) : ZMod 1982764321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1982764321 - 1) / 4657 = 425760 from by norm_num]
      have h2 : (11 : ZMod 1982764321) ^ 425760 = ((547295029 : ℕ) : ZMod 1982764321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_165393089 : Nat.Prime 165393089 := by
  refine lucas_primality 165393089 (3 : ZMod 165393089) ?_ (fun q hq hd => ?_)
  · rw [show 165393089 - 1 = 165393088 from by norm_num]
    reduce_mod_char
  · have e : 165393089 - 1 = [2 ^ 6, 7 ^ 1, 369181 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165393089 - 1) / 2 = 82696544 from by norm_num]
      have h2 : (3 : ZMod 165393089) ^ 82696544 = ((165393088 : ℕ) : ZMod 165393089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165393089 - 1) / 7 = 23627584 from by norm_num]
      have h2 : (3 : ZMod 165393089) ^ 23627584 = ((61177420 : ℕ) : ZMod 165393089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165393089 - 1) / 369181 = 448 from by norm_num]
      have h2 : (3 : ZMod 165393089) ^ 448 = ((59789304 : ℕ) : ZMod 165393089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_267301538121080056247956934369 : Nat.Prime 267301538121080056247956934369 := by
  refine lucas_primality 267301538121080056247956934369 (3 : ZMod 267301538121080056247956934369) ?_ (fun q hq hd => ?_)
  · rw [show 267301538121080056247956934369 - 1 = 267301538121080056247956934368 from by norm_num]
    reduce_mod_char
  · have e : 267301538121080056247956934369 - 1 = [2 ^ 5, 11 ^ 1, 17 ^ 1, 29 ^ 1, 907 ^ 1, 477523 ^ 1, 21502697 ^ 1, 165393089 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267301538121080056247956934369 - 1) / 2 = 133650769060540028123978467184 from by norm_num]
      have h2 : (3 : ZMod 267301538121080056247956934369) ^ 133650769060540028123978467184 = ((267301538121080056247956934368 : ℕ) : ZMod 267301538121080056247956934369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267301538121080056247956934369 - 1) / 11 = 24300139829189096022541539488 from by norm_num]
      have h2 : (3 : ZMod 267301538121080056247956934369) ^ 24300139829189096022541539488 = ((91372095363584618510672421401 : ℕ) : ZMod 267301538121080056247956934369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267301538121080056247956934369 - 1) / 17 = 15723619889475297426350407904 from by norm_num]
      have h2 : (3 : ZMod 267301538121080056247956934369) ^ 15723619889475297426350407904 = ((170675187411345337548938969214 : ℕ) : ZMod 267301538121080056247956934369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267301538121080056247956934369 - 1) / 29 = 9217294417968277801653687392 from by norm_num]
      have h2 : (3 : ZMod 267301538121080056247956934369) ^ 9217294417968277801653687392 = ((189546059939394698573592355239 : ℕ) : ZMod 267301538121080056247956934369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267301538121080056247956934369 - 1) / 907 = 294709523838015497517041824 from by norm_num]
      have h2 : (3 : ZMod 267301538121080056247956934369) ^ 294709523838015497517041824 = ((77101833157795114105838407643 : ℕ) : ZMod 267301538121080056247956934369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267301538121080056247956934369 - 1) / 477523 = 559766834521227367578016 from by norm_num]
      have h2 : (3 : ZMod 267301538121080056247956934369) ^ 559766834521227367578016 = ((174651819753876881365670841342 : ℕ) : ZMod 267301538121080056247956934369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267301538121080056247956934369 - 1) / 21502697 = 12431070303463796018144 from by norm_num]
      have h2 : (3 : ZMod 267301538121080056247956934369) ^ 12431070303463796018144 = ((153904283410357829011569723299 : ℕ) : ZMod 267301538121080056247956934369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_165393089).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267301538121080056247956934369 - 1) / 165393089 = 1616159053181962495712 from by norm_num]
      have h2 : (3 : ZMod 267301538121080056247956934369) ^ 1616159053181962495712 = ((230279647737225290648764966592 : ℕ) : ZMod 267301538121080056247956934369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_651337834379 : Nat.Prime 651337834379 := by
  refine lucas_primality 651337834379 (2 : ZMod 651337834379) ?_ (fun q hq hd => ?_)
  · rw [show 651337834379 - 1 = 651337834378 from by norm_num]
    reduce_mod_char
  · have e : 651337834379 - 1 = [2 ^ 1, 7 ^ 1, 11 ^ 1, 1013 ^ 1, 4175189 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (651337834379 - 1) / 2 = 325668917189 from by norm_num]
      have h2 : (2 : ZMod 651337834379) ^ 325668917189 = ((651337834378 : ℕ) : ZMod 651337834379) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (651337834379 - 1) / 7 = 93048262054 from by norm_num]
      have h2 : (2 : ZMod 651337834379) ^ 93048262054 = ((49644066051 : ℕ) : ZMod 651337834379) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (651337834379 - 1) / 11 = 59212530398 from by norm_num]
      have h2 : (2 : ZMod 651337834379) ^ 59212530398 = ((5721978407 : ℕ) : ZMod 651337834379) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (651337834379 - 1) / 1013 = 642979106 from by norm_num]
      have h2 : (2 : ZMod 651337834379) ^ 642979106 = ((170108133141 : ℕ) : ZMod 651337834379) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (651337834379 - 1) / 4175189 = 156002 from by norm_num]
      have h2 : (2 : ZMod 651337834379) ^ 156002 = ((411071266356 : ℕ) : ZMod 651337834379) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_80993859705028651 : Nat.Prime 80993859705028651 := by
  refine lucas_primality 80993859705028651 (2 : ZMod 80993859705028651) ?_ (fun q hq hd => ?_)
  · rw [show 80993859705028651 - 1 = 80993859705028650 from by norm_num]
    reduce_mod_char
  · have e : 80993859705028651 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 2, 829 ^ 1, 651337834379 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (80993859705028651 - 1) / 2 = 40496929852514325 from by norm_num]
      have h2 : (2 : ZMod 80993859705028651) ^ 40496929852514325 = ((80993859705028650 : ℕ) : ZMod 80993859705028651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (80993859705028651 - 1) / 3 = 26997953235009550 from by norm_num]
      have h2 : (2 : ZMod 80993859705028651) ^ 26997953235009550 = ((40538756520044952 : ℕ) : ZMod 80993859705028651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (80993859705028651 - 1) / 5 = 16198771941005730 from by norm_num]
      have h2 : (2 : ZMod 80993859705028651) ^ 16198771941005730 = ((11180339842404556 : ℕ) : ZMod 80993859705028651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (80993859705028651 - 1) / 829 = 97700675156850 from by norm_num]
      have h2 : (2 : ZMod 80993859705028651) ^ 97700675156850 = ((66364069271090438 : ℕ) : ZMod 80993859705028651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_651337834379).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (80993859705028651 - 1) / 651337834379 = 124350 from by norm_num]
      have h2 : (2 : ZMod 80993859705028651) ^ 124350 = ((24041340377656500 : ℕ) : ZMod 80993859705028651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_42514235518096149015446235113 : Nat.Prime 42514235518096149015446235113 := by
  refine lucas_primality 42514235518096149015446235113 (3 : ZMod 42514235518096149015446235113) ?_ (fun q hq hd => ?_)
  · rw [show 42514235518096149015446235113 - 1 = 42514235518096149015446235112 from by norm_num]
    reduce_mod_char
  · have e : 42514235518096149015446235113 - 1 = [2 ^ 3, 53 ^ 1, 911 ^ 1, 1358933 ^ 1, 80993859705028651 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42514235518096149015446235113 - 1) / 2 = 21257117759048074507723117556 from by norm_num]
      have h2 : (3 : ZMod 42514235518096149015446235113) ^ 21257117759048074507723117556 = ((42514235518096149015446235112 : ℕ) : ZMod 42514235518096149015446235113) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42514235518096149015446235113 - 1) / 53 = 802155387133889604065023304 from by norm_num]
      have h2 : (3 : ZMod 42514235518096149015446235113) ^ 802155387133889604065023304 = ((1638108942760784384114052930 : ℕ) : ZMod 42514235518096149015446235113) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42514235518096149015446235113 - 1) / 911 = 46667656990226288710698392 from by norm_num]
      have h2 : (3 : ZMod 42514235518096149015446235113) ^ 46667656990226288710698392 = ((5197603146166660551721046934 : ℕ) : ZMod 42514235518096149015446235113) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42514235518096149015446235113 - 1) / 1358933 = 31285012225103186849864 from by norm_num]
      have h2 : (3 : ZMod 42514235518096149015446235113) ^ 31285012225103186849864 = ((14536658073032735327335899514 : ℕ) : ZMod 42514235518096149015446235113) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_80993859705028651).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42514235518096149015446235113 - 1) / 80993859705028651 = 524906896312 from by norm_num]
      have h2 : (3 : ZMod 42514235518096149015446235113) ^ 524906896312 = ((24473438049268196451739975383 : ℕ) : ZMod 42514235518096149015446235113) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1440383213 : Nat.Prime 1440383213 := by
  refine lucas_primality 1440383213 (3 : ZMod 1440383213) ?_ (fun q hq hd => ?_)
  · rw [show 1440383213 - 1 = 1440383212 from by norm_num]
    reduce_mod_char
  · have e : 1440383213 - 1 = [2 ^ 2, 37 ^ 1, 43 ^ 1, 239 ^ 1, 947 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1440383213 - 1) / 2 = 720191606 from by norm_num]
      have h2 : (3 : ZMod 1440383213) ^ 720191606 = ((1440383212 : ℕ) : ZMod 1440383213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1440383213 - 1) / 37 = 38929276 from by norm_num]
      have h2 : (3 : ZMod 1440383213) ^ 38929276 = ((934053748 : ℕ) : ZMod 1440383213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1440383213 - 1) / 43 = 33497284 from by norm_num]
      have h2 : (3 : ZMod 1440383213) ^ 33497284 = ((1228043720 : ℕ) : ZMod 1440383213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1440383213 - 1) / 239 = 6026708 from by norm_num]
      have h2 : (3 : ZMod 1440383213) ^ 6026708 = ((114602100 : ℕ) : ZMod 1440383213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1440383213 - 1) / 947 = 1520996 from by norm_num]
      have h2 : (3 : ZMod 1440383213) ^ 1520996 = ((366065533 : ℕ) : ZMod 1440383213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2809306768001 : Nat.Prime 2809306768001 := by
  refine lucas_primality 2809306768001 (11 : ZMod 2809306768001) ?_ (fun q hq hd => ?_)
  · rw [show 2809306768001 - 1 = 2809306768000 from by norm_num]
    reduce_mod_char
  · have e : 2809306768001 - 1 = [2 ^ 7, 5 ^ 3, 953 ^ 1, 184241 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2809306768001 - 1) / 2 = 1404653384000 from by norm_num]
      have h2 : (11 : ZMod 2809306768001) ^ 1404653384000 = ((2809306768000 : ℕ) : ZMod 2809306768001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2809306768001 - 1) / 5 = 561861353600 from by norm_num]
      have h2 : (11 : ZMod 2809306768001) ^ 561861353600 = ((609090060213 : ℕ) : ZMod 2809306768001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2809306768001 - 1) / 953 = 2947856000 from by norm_num]
      have h2 : (11 : ZMod 2809306768001) ^ 2947856000 = ((2335075346968 : ℕ) : ZMod 2809306768001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2809306768001 - 1) / 184241 = 15248000 from by norm_num]
      have h2 : (11 : ZMod 2809306768001) ^ 15248000 = ((2269614486110 : ℕ) : ZMod 2809306768001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem kq_d842 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 842 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g31142213 : 31142213 ∈ P := S2 31142213 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 842 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 74))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 31142213 ∣ 2 ^ 842 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 31142213 g31142213 (by norm_num)

theorem kq_d862 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 862 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g313 : 313 ∈ P := S7 313 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g91373 : 91373 ∈ P := S2 91373 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 862 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 94))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 91373 ∣ 2 ^ 862 + 1).trans hd)
  exact absurd (S3 157 (by norm_num) (by norm_num) (hnz (by norm_num)) 313 g313 91373 g91373 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d866 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 866 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1733 : 1733 ∈ P := S2 1733 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 866 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 98))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 1733 ∣ 2 ^ 866 + 1).trans hd)
  exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 1733 g1733 (by norm_num)

theorem kq_d878 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 878 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g44210591644829 : 44210591644829 ∈ P := S2 44210591644829 prime_44210591644829 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 878 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 110))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 44210591644829 ∣ 2 ^ 878 + 1).trans hd)
  have g1568971170249692917853 : 1568971170249692917853 ∈ P := S2 1568971170249692917853 prime_1568971170249692917853 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 878 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 110))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 1568971170249692917853 ∣ 2 ^ 878 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 44210591644829 g44210591644829 1568971170249692917853 g1568971170249692917853 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d886 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 886 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g773339215189 : 773339215189 ∈ P := S2 773339215189 prime_773339215189 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 886 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 118))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 773339215189 ∣ 2 ^ 886 + 1).trans hd)
  exact S6 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 773339215189 g773339215189 (by norm_num)

theorem kq_d898 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 898 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3593 : 3593 ∈ P := S2 3593 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 898 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 130))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 3593 ∣ 2 ^ 898 + 1).trans hd)
  have g165233 : 165233 ∈ P := S2 165233 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 898 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 130))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 165233 ∣ 2 ^ 898 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 3593 g3593 165233 g165233 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d914 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 914 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6196333979234679466021864314534473 : 6196333979234679466021864314534473 ∈ P := S2 6196333979234679466021864314534473 prime_6196333979234679466021864314534473 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 914 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 146))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 6196333979234679466021864314534473 ∣ 2 ^ 914 + 1).trans hd)
  have g5845296257595668545524969937697507923682374822769 : 5845296257595668545524969937697507923682374822769 ∈ P := S2 5845296257595668545524969937697507923682374822769 prime_5845296257595668545524969937697507923682374822769 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 914 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 146))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5845296257595668545524969937697507923682374822769 ∣ 2 ^ 914 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 6196333979234679466021864314534473 g6196333979234679466021864314534473 5845296257595668545524969937697507923682374822769 g5845296257595668545524969937697507923682374822769 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d922 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 922 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g14753 : 14753 ∈ P := S2 14753 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 922 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 154))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 14753 ∣ 2 ^ 922 + 1).trans hd)
  have g7278269 : 7278269 ∈ P := S2 7278269 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 922 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 154))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 7278269 ∣ 2 ^ 922 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 14753 g14753 7278269 g7278269 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d926 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 926 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g16694937341 : 16694937341 ∈ P := S2 16694937341 prime_16694937341 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 926 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 158))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 16694937341 ∣ 2 ^ 926 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 16694937341 g16694937341 (by norm_num)

theorem kq_d934 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 934 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 : 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 ∈ P := S2 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 prime_20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 934 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 166))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 ∣ 2 ^ 934 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 g20302309294704931122598601105674308468575275657217112120355141633083494145900946314170113733 (by norm_num)

theorem kq_d958 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 958 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g9148411421 : 9148411421 ∈ P := S2 9148411421 prime_9148411421 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 958 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 190))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 9148411421 ∣ 2 ^ 958 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 9148411421 g9148411421 (by norm_num)

theorem kq_d974 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 974 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g7793 : 7793 ∈ P := S2 7793 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 974 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 206))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 7793 ∣ 2 ^ 974 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 7793 g7793 (by norm_num)

theorem kq_d982 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 982 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3929 : 3929 ∈ P := S2 3929 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 982 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 214))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 3929 ∣ 2 ^ 982 + 1).trans hd)
  have g34631213 : 34631213 ∈ P := S2 34631213 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 982 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 214))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 34631213 ∣ 2 ^ 982 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 3929 g3929 34631213 g34631213 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d998 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 998 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1997 : 1997 ∈ P := S2 1997 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 998 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 230))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 1997 ∣ 2 ^ 998 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1997 g1997 (by norm_num)

theorem kq_d1006 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1006 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g10061 : 10061 ∈ P := S2 10061 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1006 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 238))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 10061 ∣ 2 ^ 1006 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 10061 g10061 (by norm_num)

theorem kq_d1018 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1018 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4073 : 4073 ∈ P := S2 4073 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1018 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 250))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 4073 ∣ 2 ^ 1018 + 1).trans hd)
  have g103837 : 103837 ∈ P := S2 103837 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1018 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 250))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 103837 ∣ 2 ^ 1018 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 4073 g4073 103837 g103837 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1042 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1042 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g16673 : 16673 ∈ P := S2 16673 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1042 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 18)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 16673 ∣ 2 ^ 1042 + 1).trans hd)
  have g29325513271841158911701 : 29325513271841158911701 ∈ P := S2 29325513271841158911701 prime_29325513271841158911701 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1042 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 18)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 29325513271841158911701 ∣ 2 ^ 1042 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 16673 g16673 29325513271841158911701 g29325513271841158911701 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1046 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1046 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8369 : 8369 ∈ P := S2 8369 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1046 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 22)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 8369 ∣ 2 ^ 1046 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 8369 g8369 (by norm_num)

theorem kq_d1082 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1082 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8352693761 : 8352693761 ∈ P := S2 8352693761 prime_8352693761 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1082 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 58)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 8352693761 ∣ 2 ^ 1082 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 8352693761 g8352693761 (by norm_num)

theorem kq_d1094 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1094 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67887077 : 67887077 ∈ P := S2 67887077 prime_67887077 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1094 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 70)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 67887077 ∣ 2 ^ 1094 + 1).trans hd)
  have g45232564075409 : 45232564075409 ∈ P := S2 45232564075409 prime_45232564075409 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1094 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 70)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 45232564075409 ∣ 2 ^ 1094 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 67887077 g67887077 45232564075409 g45232564075409 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1114 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1114 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g91441702997 : 91441702997 ∈ P := S2 91441702997 prime_91441702997 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1114 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 90)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 91441702997 ∣ 2 ^ 1114 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 91441702997 g91441702997 (by norm_num)

theorem kq_d1126 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1126 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g51797 : 51797 ∈ P := S2 51797 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1126 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 102)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 51797 ∣ 2 ^ 1126 + 1).trans hd)
  have g133489553 : 133489553 ∈ P := S2 133489553 prime_133489553 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1126 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 102)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 133489553 ∣ 2 ^ 1126 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 51797 g51797 133489553 g133489553 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1138 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1138 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g170701 : 170701 ∈ P := S2 170701 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1138 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 114)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 170701 ∣ 2 ^ 1138 + 1).trans hd)
  have g37690561 : 37690561 ∈ P := S2 37690561 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1138 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 114)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 37690561 ∣ 2 ^ 1138 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 170701 g170701 37690561 g37690561 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1142 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1142 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g94600997 : 94600997 ∈ P := S2 94600997 prime_94600997 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1142 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 118)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 94600997 ∣ 2 ^ 1142 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 94600997 g94600997 (by norm_num)

theorem kq_d1154 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1154 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2309 : 2309 ∈ P := S2 2309 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1154 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 130)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 2309 ∣ 2 ^ 1154 + 1).trans hd)
  have g92936237 : 92936237 ∈ P := S2 92936237 prime_92936237 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1154 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 130)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 92936237 ∣ 2 ^ 1154 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 2309 g2309 92936237 g92936237 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1174 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1174 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2434616217281 : 2434616217281 ∈ P := S2 2434616217281 prime_2434616217281 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1174 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 150)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 2434616217281 ∣ 2 ^ 1174 + 1).trans hd)
  have g394226184349830246792353594915553669141480163076208147970769 : 394226184349830246792353594915553669141480163076208147970769 ∈ P := S2 394226184349830246792353594915553669141480163076208147970769 prime_394226184349830246792353594915553669141480163076208147970769 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1174 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 150)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 394226184349830246792353594915553669141480163076208147970769 ∣ 2 ^ 1174 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 2434616217281 g2434616217281 394226184349830246792353594915553669141480163076208147970769 g394226184349830246792353594915553669141480163076208147970769 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1186 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1186 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g23360190343863455255753897 : 23360190343863455255753897 ∈ P := S2 23360190343863455255753897 prime_23360190343863455255753897 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1186 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 162)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 23360190343863455255753897 ∣ 2 ^ 1186 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 23360190343863455255753897 g23360190343863455255753897 (by norm_num)

theorem kq_d1198 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1198 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4793 : 4793 ∈ P := S2 4793 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1198 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 174)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 4793 ∣ 2 ^ 1198 + 1).trans hd)
  have g86257 : 86257 ∈ P := S2 86257 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1198 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 174)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 86257 ∣ 2 ^ 1198 + 1).trans hd)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 4793 g4793 86257 g86257 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1214 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1214 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6391568743817 : 6391568743817 ∈ P := S2 6391568743817 prime_6391568743817 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1214 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 190)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 6391568743817 ∣ 2 ^ 1214 + 1).trans hd)
  have g2366069394177173 : 2366069394177173 ∈ P := S2 2366069394177173 prime_2366069394177173 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1214 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 190)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 2366069394177173 ∣ 2 ^ 1214 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 6391568743817 g6391568743817 2366069394177173 g2366069394177173 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1226 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1226 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g18201416023204829 : 18201416023204829 ∈ P := S2 18201416023204829 prime_18201416023204829 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1226 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 202)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 18201416023204829 ∣ 2 ^ 1226 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 18201416023204829 g18201416023204829 (by norm_num)

theorem kq_d1234 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1234 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g86381 : 86381 ∈ P := S2 86381 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1234 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 210)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 86381 ∣ 2 ^ 1234 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 86381 g86381 (by norm_num)

theorem kq_d1238 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1238 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g284741 : 284741 ∈ P := S2 284741 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1238 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 214)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 284741 ∣ 2 ^ 1238 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 284741 g284741 (by norm_num)

theorem kq_d1262 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1262 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g328121 : 328121 ∈ P := S2 328121 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1262 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 238)))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 328121 ∣ 2 ^ 1262 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 328121 g328121 (by norm_num)

theorem kq_d1282 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1282 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g62248793 : 62248793 ∈ P := S2 62248793 prime_62248793 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1282 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 2))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 62248793 ∣ 2 ^ 1282 + 1).trans hd)
  have g813428186489554222340095640950541 : 813428186489554222340095640950541 ∈ P := S2 813428186489554222340095640950541 prime_813428186489554222340095640950541 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1282 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 2))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 813428186489554222340095640950541 ∣ 2 ^ 1282 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 62248793 g62248793 813428186489554222340095640950541 g813428186489554222340095640950541 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1286 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1286 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5926025872693688636842717229 : 5926025872693688636842717229 ∈ P := S2 5926025872693688636842717229 prime_5926025872693688636842717229 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1286 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 6))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 5926025872693688636842717229 ∣ 2 ^ 1286 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 5926025872693688636842717229 g5926025872693688636842717229 (by norm_num)

theorem kq_d1294 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1294 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g9679121 : 9679121 ∈ P := S2 9679121 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1294 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 14))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 9679121 ∣ 2 ^ 1294 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 9679121 g9679121 (by norm_num)

theorem kq_d1318 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1318 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5273 : 5273 ∈ P := S2 5273 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1318 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 38))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 5273 ∣ 2 ^ 1318 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 5273 g5273 (by norm_num)

theorem kq_d1322 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1322 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g313 : 313 ∈ P := S7 313 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g157 : 157 ∈ P := S1 157 (by norm_num) (by norm_num) (hnz (by norm_num)) 313 g313 (by norm_num)
  have g6608806553038710269510748680377 : 6608806553038710269510748680377 ∈ P := S2 6608806553038710269510748680377 prime_6608806553038710269510748680377 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1322 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 42))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 6608806553038710269510748680377 ∣ 2 ^ 1322 + 1).trans hd)
  exact absurd (S3 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 157 g157 6608806553038710269510748680377 g6608806553038710269510748680377 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1346 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1346 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2693 : 2693 ∈ P := S2 2693 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1346 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 66))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 2693 ∣ 2 ^ 1346 + 1).trans hd)
  have g26921 : 26921 ∈ P := S2 26921 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1346 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 66))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 26921 ∣ 2 ^ 1346 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 2693 g2693 26921 g26921 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1354 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1354 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5417 : 5417 ∈ P := S2 5417 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1354 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 74))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 5417 ∣ 2 ^ 1354 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 5417 g5417 (by norm_num)

theorem kq_d1382 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1382 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g77323353608284863403150817040930314294291149972109317262405018115863298721488023177 : 77323353608284863403150817040930314294291149972109317262405018115863298721488023177 ∈ P := S2 77323353608284863403150817040930314294291149972109317262405018115863298721488023177 prime_77323353608284863403150817040930314294291149972109317262405018115863298721488023177 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1382 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 102))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 77323353608284863403150817040930314294291149972109317262405018115863298721488023177 ∣ 2 ^ 1382 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 77323353608284863403150817040930314294291149972109317262405018115863298721488023177 g77323353608284863403150817040930314294291149972109317262405018115863298721488023177 (by norm_num)

theorem kq_d1402 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1402 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4846812462461 : 4846812462461 ∈ P := S2 4846812462461 prime_4846812462461 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1402 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 122))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 4846812462461 ∣ 2 ^ 1402 + 1).trans hd)
  have g16494815758321902827664653884456105022034001119493371936617 : 16494815758321902827664653884456105022034001119493371936617 ∈ P := S2 16494815758321902827664653884456105022034001119493371936617 prime_16494815758321902827664653884456105022034001119493371936617 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1402 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 122))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 16494815758321902827664653884456105022034001119493371936617 ∣ 2 ^ 1402 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 4846812462461 g4846812462461 16494815758321902827664653884456105022034001119493371936617 g16494815758321902827664653884456105022034001119493371936617 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1418 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1418 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2837 : 2837 ∈ P := S2 2837 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1418 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 138))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 2837 ∣ 2 ^ 1418 + 1).trans hd)
  have g870732921536023739754807103419461 : 870732921536023739754807103419461 ∈ P := S2 870732921536023739754807103419461 prime_870732921536023739754807103419461 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1418 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 138))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 870732921536023739754807103419461 ∣ 2 ^ 1418 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 2837 g2837 870732921536023739754807103419461 g870732921536023739754807103419461 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1438 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1438 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g31072352777637469858310183672941789 : 31072352777637469858310183672941789 ∈ P := S2 31072352777637469858310183672941789 prime_31072352777637469858310183672941789 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1438 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 158))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 31072352777637469858310183672941789 ∣ 2 ^ 1438 + 1).trans hd)
  have g155046904371518383134460036224501936457 : 155046904371518383134460036224501936457 ∈ P := S2 155046904371518383134460036224501936457 prime_155046904371518383134460036224501936457 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1438 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 158))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 155046904371518383134460036224501936457 ∣ 2 ^ 1438 + 1).trans hd)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 31072352777637469858310183672941789 g31072352777637469858310183672941789 155046904371518383134460036224501936457 g155046904371518383134460036224501936457 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1454 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1454 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g857549407959771467593127178673816649389585714165937 : 857549407959771467593127178673816649389585714165937 ∈ P := S2 857549407959771467593127178673816649389585714165937 prime_857549407959771467593127178673816649389585714165937 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1454 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 174))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 857549407959771467593127178673816649389585714165937 ∣ 2 ^ 1454 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 857549407959771467593127178673816649389585714165937 g857549407959771467593127178673816649389585714165937 (by norm_num)

theorem kq_d1466 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1466 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g627449 : 627449 ∈ P := S2 627449 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1466 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 186))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 627449 ∣ 2 ^ 1466 + 1).trans hd)
  have g205726455772006440377818607135775827053674474181634602781 : 205726455772006440377818607135775827053674474181634602781 ∈ P := S2 205726455772006440377818607135775827053674474181634602781 prime_205726455772006440377818607135775827053674474181634602781 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1466 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 186))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 205726455772006440377818607135775827053674474181634602781 ∣ 2 ^ 1466 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 627449 g627449 205726455772006440377818607135775827053674474181634602781 g205726455772006440377818607135775827053674474181634602781 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1478 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1478 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2957 : 2957 ∈ P := S2 2957 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1478 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 198))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 2957 ∣ 2 ^ 1478 + 1).trans hd)
  have g6139613 : 6139613 ∈ P := S2 6139613 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1478 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 198))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 6139613 ∣ 2 ^ 1478 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 2957 g2957 6139613 g6139613 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1486 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1486 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g260683037 : 260683037 ∈ P := S2 260683037 prime_260683037 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1486 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 206))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 260683037 ∣ 2 ^ 1486 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 260683037 g260683037 (by norm_num)

theorem kq_d1514 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1514 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g15546196279794280749075061880957 : 15546196279794280749075061880957 ∈ P := S2 15546196279794280749075061880957 prime_15546196279794280749075061880957 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1514 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 234))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 15546196279794280749075061880957 ∣ 2 ^ 1514 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 15546196279794280749075061880957 g15546196279794280749075061880957 (by norm_num)

theorem kq_d1522 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1522 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1567661 : 1567661 ∈ P := S2 1567661 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1522 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 242))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 1567661 ∣ 2 ^ 1522 + 1).trans hd)
  have g1168457387724788393 : 1168457387724788393 ∈ P := S2 1168457387724788393 prime_1168457387724788393 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1522 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 242))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 1168457387724788393 ∣ 2 ^ 1522 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1567661 g1567661 1168457387724788393 g1168457387724788393 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1538 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1538 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1508116661 : 1508116661 ∈ P := S2 1508116661 prime_1508116661 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1538 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 2)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 1508116661 ∣ 2 ^ 1538 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1508116661 g1508116661 (by norm_num)

theorem kq_d1546 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1546 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g961613 : 961613 ∈ P := S2 961613 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1546 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 10)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 961613 ∣ 2 ^ 1546 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 961613 g961613 (by norm_num)

theorem kq_d1574 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1574 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g14121929 : 14121929 ∈ P := S2 14121929 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1574 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 38)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 14121929 ∣ 2 ^ 1574 + 1).trans hd)
  have g50902080564527017360173061387390051814344996542268977221 : 50902080564527017360173061387390051814344996542268977221 ∈ P := S2 50902080564527017360173061387390051814344996542268977221 prime_50902080564527017360173061387390051814344996542268977221 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1574 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 38)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 50902080564527017360173061387390051814344996542268977221 ∣ 2 ^ 1574 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 14121929 g14121929 50902080564527017360173061387390051814344996542268977221 g50902080564527017360173061387390051814344996542268977221 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1594 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1594 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1131019499249 : 1131019499249 ∈ P := S2 1131019499249 prime_1131019499249 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1594 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 58)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 1131019499249 ∣ 2 ^ 1594 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1131019499249 g1131019499249 (by norm_num)

theorem kq_d1618 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1618 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6473 : 6473 ∈ P := S2 6473 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1618 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 82)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 6473 ∣ 2 ^ 1618 + 1).trans hd)
  have g25889 : 25889 ∈ P := S2 25889 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1618 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 82)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 25889 ∣ 2 ^ 1618 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 6473 g6473 25889 g25889 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1646 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1646 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g924509587369596772157 : 924509587369596772157 ∈ P := S2 924509587369596772157 prime_924509587369596772157 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1646 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 110)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 924509587369596772157 ∣ 2 ^ 1646 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 924509587369596772157 g924509587369596772157 (by norm_num)

theorem kq_d1654 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1654 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g148861 : 148861 ∈ P := S2 148861 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1654 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 118)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 148861 ∣ 2 ^ 1654 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 148861 g148861 (by norm_num)

theorem kq_d1658 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1658 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g12624459932825972330038421 : 12624459932825972330038421 ∈ P := S2 12624459932825972330038421 prime_12624459932825972330038421 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1658 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 122)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 12624459932825972330038421 ∣ 2 ^ 1658 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 12624459932825972330038421 g12624459932825972330038421 (by norm_num)

theorem kq_d1678 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1678 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5564249 : 5564249 ∈ P := S2 5564249 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1678 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 142)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 5564249 ∣ 2 ^ 1678 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 5564249 g5564249 (by norm_num)

theorem kq_d1706 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1706 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3413 : 3413 ∈ P := S2 3413 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1706 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 170)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 3413 ∣ 2 ^ 1706 + 1).trans hd)
  have g1122047772459197542365557 : 1122047772459197542365557 ∈ P := S2 1122047772459197542365557 prime_1122047772459197542365557 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1706 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 170)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 1122047772459197542365557 ∣ 2 ^ 1706 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 3413 g3413 1122047772459197542365557 g1122047772459197542365557 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1714 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1714 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g51158163991710264101 : 51158163991710264101 ∈ P := S2 51158163991710264101 prime_51158163991710264101 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1714 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 178)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 51158163991710264101 ∣ 2 ^ 1714 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 51158163991710264101 g51158163991710264101 (by norm_num)

theorem kq_d1718 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1718 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g18970157 : 18970157 ∈ P := S2 18970157 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1718 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 182)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 18970157 ∣ 2 ^ 1718 + 1).trans hd)
  have g82488053 : 82488053 ∈ P := S2 82488053 prime_82488053 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1718 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 182)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 82488053 ∣ 2 ^ 1718 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 18970157 g18970157 82488053 g82488053 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1726 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1726 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41734812223623741861146169997 : 41734812223623741861146169997 ∈ P := S2 41734812223623741861146169997 prime_41734812223623741861146169997 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1726 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 190)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 41734812223623741861146169997 ∣ 2 ^ 1726 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41734812223623741861146169997 g41734812223623741861146169997 (by norm_num)

theorem kq_d1754 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1754 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8045864609 : 8045864609 ∈ P := S2 8045864609 prime_8045864609 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1754 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 218)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 8045864609 ∣ 2 ^ 1754 + 1).trans hd)
  have g94177931835255001 : 94177931835255001 ∈ P := S2 94177931835255001 prime_94177931835255001 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1754 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 218)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 94177931835255001 ∣ 2 ^ 1754 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 8045864609 g8045864609 94177931835255001 g94177931835255001 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1762 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1762 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g292493 : 292493 ∈ P := S2 292493 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1762 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 226)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 292493 ∣ 2 ^ 1762 + 1).trans hd)
  exact S6 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 292493 g292493 (by norm_num)

theorem kq_d1766 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1766 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g9642835106981 : 9642835106981 ∈ P := S2 9642835106981 prime_9642835106981 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1766 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 230)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 9642835106981 ∣ 2 ^ 1766 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 9642835106981 g9642835106981 (by norm_num)

theorem kq_d1774 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1774 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1982764321 : 1982764321 ∈ P := S2 1982764321 prime_1982764321 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1774 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 238)))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 1982764321 ∣ 2 ^ 1774 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1982764321 g1982764321 (by norm_num)

theorem kq_d1814 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1814 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g267301538121080056247956934369 : 267301538121080056247956934369 ∈ P := S2 267301538121080056247956934369 prime_267301538121080056247956934369 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1814 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 22))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 267301538121080056247956934369 ∣ 2 ^ 1814 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 267301538121080056247956934369 g267301538121080056247956934369 (by norm_num)

theorem kq_d1822 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1822 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g29153 : 29153 ∈ P := S2 29153 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1822 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 30))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 29153 ∣ 2 ^ 1822 + 1).trans hd)
  have g42514235518096149015446235113 : 42514235518096149015446235113 ∈ P := S2 42514235518096149015446235113 prime_42514235518096149015446235113 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1822 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 30))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 42514235518096149015446235113 ∣ 2 ^ 1822 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 29153 g29153 42514235518096149015446235113 g42514235518096149015446235113 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1838 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1838 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3677 : 3677 ∈ P := S2 3677 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1838 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 46))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 3677 ∣ 2 ^ 1838 + 1).trans hd)
  have g169097 : 169097 ∈ P := S2 169097 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1838 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 46))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 169097 ∣ 2 ^ 1838 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 3677 g3677 169097 g169097 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1858 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1858 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g7433 : 7433 ∈ P := S2 7433 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1858 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 66))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 7433 ∣ 2 ^ 1858 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 7433 g7433 (by norm_num)

theorem kq_d1874 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1874 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g802073 : 802073 ∈ P := S2 802073 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1874 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 82))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 802073 ∣ 2 ^ 1874 + 1).trans hd)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 802073 g802073 (by norm_num)

theorem kq_d1882 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1882 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3383837 : 3383837 ∈ P := S2 3383837 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1882 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 90))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 3383837 ∣ 2 ^ 1882 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 3383837 g3383837 (by norm_num)

theorem kq_d1894 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1894 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g189401 : 189401 ∈ P := S2 189401 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1894 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 102))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 189401 ∣ 2 ^ 1894 + 1).trans hd)
  have g1440383213 : 1440383213 ∈ P := S2 1440383213 prime_1440383213 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1894 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 102))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 1440383213 ∣ 2 ^ 1894 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 189401 g189401 1440383213 g1440383213 (by norm_num) (by norm_num)) (by norm_num)

theorem kq_d1906 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1906 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2809306768001 : 2809306768001 ∈ P := S2 2809306768001 prime_2809306768001 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1906 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 114))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 2809306768001 ∣ 2 ^ 1906 + 1).trans hd)
  exact S6 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 2809306768001 g2809306768001 (by norm_num)

theorem kq_d1942 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1942 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g19421 : 19421 ∈ P := S2 19421 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1942 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 150))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 19421 ∣ 2 ^ 1942 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 19421 g19421 (by norm_num)

theorem kq_d1994 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 1994 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1316041 : 1316041 ∈ P := S2 1316041 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1994 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 202))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 1316041 ∣ 2 ^ 1994 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1316041 g1316041 (by norm_num)

theorem kq_d2026 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5P : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 2026 + 1 ∣ 2 ^ m + 1) : False := by
  have hK := hK5 4
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g33449261 : 33449261 ∈ P := S2 33449261 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 2026 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 234))))))) from by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]]; norm_num : 33449261 ∣ 2 ^ 2026 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 33449261 g33449261 (by norm_num)

-- Section 2. The new sieve.

set_option maxHeartbeats 4000000 in
theorem nsieve_0 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (h4 : m % 4 = 2) :
    ∀ q ∈ ({421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587} : Finset ℕ), ¬ q ∣ m := by
  intro q hq hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kq_d842 hP h5 E (tpd (d := 842) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d862 hP h5 E (tpd (d := 862) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d866 hP h5 E (tpd (d := 866) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d878 hP h5 E (tpd (d := 878) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d886 hP h5 E (tpd (d := 886) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d898 hP h5 E (tpd (d := 898) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d914 hP h5 E (tpd (d := 914) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d922 hP h5 E (tpd (d := 922) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d926 hP h5 E (tpd (d := 926) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d934 hP h5 E (tpd (d := 934) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d958 hP h5 E (tpd (d := 958) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d974 hP h5 E (tpd (d := 974) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d982 hP h5 E (tpd (d := 982) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d998 hP h5 E (tpd (d := 998) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1006 hP h5 E (tpd (d := 1006) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1018 hP h5 E (tpd (d := 1018) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1042 hP h5 E (tpd (d := 1042) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1046 hP h5 E (tpd (d := 1046) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1082 hP h5 E (tpd (d := 1082) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1094 hP h5 E (tpd (d := 1094) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1114 hP h5 E (tpd (d := 1114) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1126 hP h5 E (tpd (d := 1126) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1138 hP h5 E (tpd (d := 1138) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1142 hP h5 E (tpd (d := 1142) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1154 hP h5 E (tpd (d := 1154) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1174 hP h5 E (tpd (d := 1174) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))

set_option maxHeartbeats 4000000 in
theorem nsieve_1 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (h4 : m % 4 = 2) :
    ∀ q ∈ ({593, 599, 607, 613, 617, 619, 631, 641, 643, 647, 659, 661, 673, 677, 691, 701, 709, 719, 727, 733, 739, 743, 757, 761, 769, 773} : Finset ℕ), ¬ q ∣ m := by
  intro q hq hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kq_d1186 hP h5 E (tpd (d := 1186) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1198 hP h5 E (tpd (d := 1198) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1214 hP h5 E (tpd (d := 1214) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1226 hP h5 E (tpd (d := 1226) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1234 hP h5 E (tpd (d := 1234) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1238 hP h5 E (tpd (d := 1238) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1262 hP h5 E (tpd (d := 1262) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1282 hP h5 E (tpd (d := 1282) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1286 hP h5 E (tpd (d := 1286) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1294 hP h5 E (tpd (d := 1294) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1318 hP h5 E (tpd (d := 1318) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1322 hP h5 E (tpd (d := 1322) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1346 hP h5 E (tpd (d := 1346) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1354 hP h5 E (tpd (d := 1354) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1382 hP h5 E (tpd (d := 1382) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1402 hP h5 E (tpd (d := 1402) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1418 hP h5 E (tpd (d := 1418) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1438 hP h5 E (tpd (d := 1438) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1454 hP h5 E (tpd (d := 1454) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1466 hP h5 E (tpd (d := 1466) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1478 hP h5 E (tpd (d := 1478) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1486 hP h5 E (tpd (d := 1486) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1514 hP h5 E (tpd (d := 1514) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1522 hP h5 E (tpd (d := 1522) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1538 hP h5 E (tpd (d := 1538) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1546 hP h5 E (tpd (d := 1546) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))

set_option maxHeartbeats 4000000 in
theorem nsieve_2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (h4 : m % 4 = 2) :
    ∀ q ∈ ({787, 797, 809, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 971, 997, 1013} : Finset ℕ), ¬ q ∣ m := by
  intro q hq hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kq_d1574 hP h5 E (tpd (d := 1574) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1594 hP h5 E (tpd (d := 1594) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1618 hP h5 E (tpd (d := 1618) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1646 hP h5 E (tpd (d := 1646) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1654 hP h5 E (tpd (d := 1654) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1658 hP h5 E (tpd (d := 1658) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1678 hP h5 E (tpd (d := 1678) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1706 hP h5 E (tpd (d := 1706) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1714 hP h5 E (tpd (d := 1714) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1718 hP h5 E (tpd (d := 1718) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1726 hP h5 E (tpd (d := 1726) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1754 hP h5 E (tpd (d := 1754) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1762 hP h5 E (tpd (d := 1762) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1766 hP h5 E (tpd (d := 1766) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1774 hP h5 E (tpd (d := 1774) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1814 hP h5 E (tpd (d := 1814) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1822 hP h5 E (tpd (d := 1822) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1838 hP h5 E (tpd (d := 1838) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1858 hP h5 E (tpd (d := 1858) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1874 hP h5 E (tpd (d := 1874) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1882 hP h5 E (tpd (d := 1882) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1894 hP h5 E (tpd (d := 1894) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1906 hP h5 E (tpd (d := 1906) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1942 hP h5 E (tpd (d := 1942) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d1994 hP h5 E (tpd (d := 1994) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))
  · exact kq_d2026 hP h5 E (tpd (d := 2026) (by have h' := mod_of_dvd_two_mod_four hd (by norm_num) h4; norm_num at h'; exact h'))

set_option maxHeartbeats 4000000 in
theorem nsieve {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (h4 : m % 4 = 2) :
    ∀ q ∈ ({421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 607, 613, 617, 619, 631, 641, 643, 647, 659, 661, 673, 677, 691, 701, 709, 719, 727, 733, 739, 743, 757, 761, 769, 773, 787, 797, 809, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 971, 997, 1013} : Finset ℕ), ¬ q ∣ m := by
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nsieve_0 hP h5 E h4 421 (by simp)
  · exact nsieve_0 hP h5 E h4 431 (by simp)
  · exact nsieve_0 hP h5 E h4 433 (by simp)
  · exact nsieve_0 hP h5 E h4 439 (by simp)
  · exact nsieve_0 hP h5 E h4 443 (by simp)
  · exact nsieve_0 hP h5 E h4 449 (by simp)
  · exact nsieve_0 hP h5 E h4 457 (by simp)
  · exact nsieve_0 hP h5 E h4 461 (by simp)
  · exact nsieve_0 hP h5 E h4 463 (by simp)
  · exact nsieve_0 hP h5 E h4 467 (by simp)
  · exact nsieve_0 hP h5 E h4 479 (by simp)
  · exact nsieve_0 hP h5 E h4 487 (by simp)
  · exact nsieve_0 hP h5 E h4 491 (by simp)
  · exact nsieve_0 hP h5 E h4 499 (by simp)
  · exact nsieve_0 hP h5 E h4 503 (by simp)
  · exact nsieve_0 hP h5 E h4 509 (by simp)
  · exact nsieve_0 hP h5 E h4 521 (by simp)
  · exact nsieve_0 hP h5 E h4 523 (by simp)
  · exact nsieve_0 hP h5 E h4 541 (by simp)
  · exact nsieve_0 hP h5 E h4 547 (by simp)
  · exact nsieve_0 hP h5 E h4 557 (by simp)
  · exact nsieve_0 hP h5 E h4 563 (by simp)
  · exact nsieve_0 hP h5 E h4 569 (by simp)
  · exact nsieve_0 hP h5 E h4 571 (by simp)
  · exact nsieve_0 hP h5 E h4 577 (by simp)
  · exact nsieve_0 hP h5 E h4 587 (by simp)
  · exact nsieve_1 hP h5 E h4 593 (by simp)
  · exact nsieve_1 hP h5 E h4 599 (by simp)
  · exact nsieve_1 hP h5 E h4 607 (by simp)
  · exact nsieve_1 hP h5 E h4 613 (by simp)
  · exact nsieve_1 hP h5 E h4 617 (by simp)
  · exact nsieve_1 hP h5 E h4 619 (by simp)
  · exact nsieve_1 hP h5 E h4 631 (by simp)
  · exact nsieve_1 hP h5 E h4 641 (by simp)
  · exact nsieve_1 hP h5 E h4 643 (by simp)
  · exact nsieve_1 hP h5 E h4 647 (by simp)
  · exact nsieve_1 hP h5 E h4 659 (by simp)
  · exact nsieve_1 hP h5 E h4 661 (by simp)
  · exact nsieve_1 hP h5 E h4 673 (by simp)
  · exact nsieve_1 hP h5 E h4 677 (by simp)
  · exact nsieve_1 hP h5 E h4 691 (by simp)
  · exact nsieve_1 hP h5 E h4 701 (by simp)
  · exact nsieve_1 hP h5 E h4 709 (by simp)
  · exact nsieve_1 hP h5 E h4 719 (by simp)
  · exact nsieve_1 hP h5 E h4 727 (by simp)
  · exact nsieve_1 hP h5 E h4 733 (by simp)
  · exact nsieve_1 hP h5 E h4 739 (by simp)
  · exact nsieve_1 hP h5 E h4 743 (by simp)
  · exact nsieve_1 hP h5 E h4 757 (by simp)
  · exact nsieve_1 hP h5 E h4 761 (by simp)
  · exact nsieve_1 hP h5 E h4 769 (by simp)
  · exact nsieve_1 hP h5 E h4 773 (by simp)
  · exact nsieve_2 hP h5 E h4 787 (by simp)
  · exact nsieve_2 hP h5 E h4 797 (by simp)
  · exact nsieve_2 hP h5 E h4 809 (by simp)
  · exact nsieve_2 hP h5 E h4 823 (by simp)
  · exact nsieve_2 hP h5 E h4 827 (by simp)
  · exact nsieve_2 hP h5 E h4 829 (by simp)
  · exact nsieve_2 hP h5 E h4 839 (by simp)
  · exact nsieve_2 hP h5 E h4 853 (by simp)
  · exact nsieve_2 hP h5 E h4 857 (by simp)
  · exact nsieve_2 hP h5 E h4 859 (by simp)
  · exact nsieve_2 hP h5 E h4 863 (by simp)
  · exact nsieve_2 hP h5 E h4 877 (by simp)
  · exact nsieve_2 hP h5 E h4 881 (by simp)
  · exact nsieve_2 hP h5 E h4 883 (by simp)
  · exact nsieve_2 hP h5 E h4 887 (by simp)
  · exact nsieve_2 hP h5 E h4 907 (by simp)
  · exact nsieve_2 hP h5 E h4 911 (by simp)
  · exact nsieve_2 hP h5 E h4 919 (by simp)
  · exact nsieve_2 hP h5 E h4 929 (by simp)
  · exact nsieve_2 hP h5 E h4 937 (by simp)
  · exact nsieve_2 hP h5 E h4 941 (by simp)
  · exact nsieve_2 hP h5 E h4 947 (by simp)
  · exact nsieve_2 hP h5 E h4 953 (by simp)
  · exact nsieve_2 hP h5 E h4 971 (by simp)
  · exact nsieve_2 hP h5 E h4 997 (by simp)
  · exact nsieve_2 hP h5 E h4 1013 (by simp)

-- Section 3. The step.

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨A1 + A2, fun n h hS he h4 hbig hsv h15 h25 h27 => ?_⟩
  obtain ⟨hP, h5, E⟩ := setup h hS
  rw [he] at E
  have hns := nsieve hP h5 E h4
  by_cases hsm : 3 ∣ padicValNat 2 n ∨ 5 ∣ padicValNat 2 n
  · have := h1 n h hS he h4 hbig hsv h15 h25 h27 hns hsm
    omega
  · simp only [not_or] at hsm
    have := h2 n h hS he h4 hbig hsv h15 h25 h27 hns hsm.1 hsm.2
    omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1_H1_R1
