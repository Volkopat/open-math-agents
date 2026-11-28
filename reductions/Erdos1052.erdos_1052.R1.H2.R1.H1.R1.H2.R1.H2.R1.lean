import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H2.R1
-- Upstream path: reductions/Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H2.R1.lean
-- Credit: @adammcarter (agent: Claude Code, model claude-fable-5-2)
--
-- Splits step H2 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1 (5 is the only repeated odd prime of
-- the unitary perfect number n, 5^4 exactly divides n, a = padicValNat 2 n is even, a >= 128 and
-- v2(a) is not in R5) by the power of 2 dividing a, after sieving the class a = 2 mod 4.
-- Proving H1, ..., H4 proves the step.
--
-- Notation as in the parent file: P = the set of simple odd primes of n.  The balance equation is
--   (2^a + 1)(1 + 5^4) prod_P (p + 1) = 2^(a+1) 5^4 prod_P p,
-- in which every odd prime other than 5 (so also 3) occurs exactly once on the left and 5 occurs
-- exactly 4 times.  Here 1 + 5^4 = 2 * 313, so 313, 157 (314 = 2 * 157) and 79 (158 = 2 * 79) are
-- simple primes of n, and 80 = 16 * 5 uses one of the four factors of 5.
--
-- PROVED BELOW (no hypothesis needed):
--  * classes: a even and v2(a) not in R5 leaves v2(a) = 1, v2(a) = 20, v2(a) = 24 or 2^33 | a
--    (R5 = {2, ..., 19, 21, 22, 23, 25, ..., 32} comes from known factors of Fermat numbers; no
--    factor of F20 or F24 is known).
--  * sieve: if a = 2 mod 4 then no prime q with 7 <= q <= 420 divides a, and 15, 25, 27 do not
--    divide a.  So a = 2 * 3^i * 5^j * (primes above 420) with (i, j) = (0,0), (1,0), (2,0) or (0,1).
--    One lemma k_q<q> per q (81 of them): if q divides a then 2^(2q) + 1 divides 2^a + 1, its prime
--    factors are simple primes of n, the odd primes of p + 1 for simple p are simple again, and
--    the chain ends at a prime with two sources on the left (24 cases; very often the prime 3:
--    a is even, so 3 does not divide 2^a + 1 and at most one simple prime is 2 mod 3), at a
--    square (55 cases; very often 9 dividing p + 1) or at more than four factors of 5 (2 cases).
--    Primes above 4.3 * 10^7 carry a Lucas certificate (theorems prime_<p>, 24 new, up to 85
--    digits).
-- The classes q = 3, 5, 9 cannot be sieved this way: the forced primes are consistent, and for
-- q = 9 (a = 18) they are exactly the primes of Wall's number
-- 2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313, which is unitary perfect; the
-- parent's a >= 128 is what excludes it.
--
-- H1 (OPEN): a = 2 mod 4, with the sieve.
-- H2 (OPEN): v2(a) = 20.     H3 (OPEN): v2(a) = 24.     H4 (OPEN): 2^33 divides a.
-- No known unitary perfect number satisfies the hypotheses of any H.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main

-- H1: a is bounded when a = 2 mod 4, a >= 128, no prime q with 7 <= q <= 420 divides a, and
-- 15, 25, 27 do not divide a.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 4 →
    padicValNat 2 n % 4 = 2 → 128 ≤ padicValNat 2 n →
    (∀ q, q.Prime → 7 ≤ q → q ≤ 420 → ¬ q ∣ padicValNat 2 n) →
    ¬ 15 ∣ padicValNat 2 n → ¬ 25 ∣ padicValNat 2 n → ¬ 27 ∣ padicValNat 2 n →
    padicValNat 2 n ≤ A

-- H2: a is bounded when v2(a) = 20.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 4 →
    padicValNat 2 n % 2 ^ 21 = 2 ^ 20 →
    padicValNat 2 n ≤ A

-- H3: a is bounded when v2(a) = 24.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 4 →
    padicValNat 2 n % 2 ^ 25 = 2 ^ 24 →
    padicValNat 2 n ≤ A

-- H4: a is bounded when 2^33 divides a.
def H4 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 4 →
    padicValNat 2 n % 2 ^ 33 = 0 →
    padicValNat 2 n ≤ A

-- Section 1. Lucas certificates, the forced-chain lemmas and the sieve.

theorem prime_536903681 : Nat.Prime 536903681 := by
  refine lucas_primality 536903681 (7 : ZMod 536903681) ?_ (fun q hq hd => ?_)
  · rw [show 536903681 - 1 = 536903680 from by norm_num]
    reduce_mod_char
  · have e : 536903681 - 1 = [2 ^ 15, 5 ^ 1, 29 ^ 1, 113 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (536903681 - 1) / 2 = 268451840 from by norm_num]
      have h2 : (7 : ZMod 536903681) ^ 268451840 = ((536903680 : ℕ) : ZMod 536903681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (536903681 - 1) / 5 = 107380736 from by norm_num]
      have h2 : (7 : ZMod 536903681) ^ 107380736 = ((215678328 : ℕ) : ZMod 536903681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (536903681 - 1) / 29 = 18513920 from by norm_num]
      have h2 : (7 : ZMod 536903681) ^ 18513920 = ((524320 : ℕ) : ZMod 536903681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (536903681 - 1) / 113 = 4751360 from by norm_num]
      have h2 : (7 : ZMod 536903681) ^ 4751360 = ((318081945 : ℕ) : ZMod 536903681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4999465853 : Nat.Prime 4999465853 := by
  refine lucas_primality 4999465853 (3 : ZMod 4999465853) ?_ (fun q hq hd => ?_)
  · rw [show 4999465853 - 1 = 4999465852 from by norm_num]
    reduce_mod_char
  · have e : 4999465853 - 1 = [2 ^ 2, 31 ^ 1, 71 ^ 1, 567863 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4999465853 - 1) / 2 = 2499732926 from by norm_num]
      have h2 : (3 : ZMod 4999465853) ^ 2499732926 = ((4999465852 : ℕ) : ZMod 4999465853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4999465853 - 1) / 31 = 161273092 from by norm_num]
      have h2 : (3 : ZMod 4999465853) ^ 161273092 = ((893418988 : ℕ) : ZMod 4999465853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4999465853 - 1) / 71 = 70415012 from by norm_num]
      have h2 : (3 : ZMod 4999465853) ^ 70415012 = ((185429958 : ℕ) : ZMod 4999465853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4999465853 - 1) / 567863 = 8804 from by norm_num]
      have h2 : (3 : ZMod 4999465853) ^ 8804 = ((3753691010 : ℕ) : ZMod 4999465853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_269665073 : Nat.Prime 269665073 := by
  refine lucas_primality 269665073 (3 : ZMod 269665073) ?_ (fun q hq hd => ?_)
  · rw [show 269665073 - 1 = 269665072 from by norm_num]
    reduce_mod_char
  · have e : 269665073 - 1 = [2 ^ 4, 131 ^ 1, 128657 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269665073 - 1) / 2 = 134832536 from by norm_num]
      have h2 : (3 : ZMod 269665073) ^ 134832536 = ((269665072 : ℕ) : ZMod 269665073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269665073 - 1) / 131 = 2058512 from by norm_num]
      have h2 : (3 : ZMod 269665073) ^ 2058512 = ((208315157 : ℕ) : ZMod 269665073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269665073 - 1) / 128657 = 2096 from by norm_num]
      have h2 : (3 : ZMod 269665073) ^ 2096 = ((221449475 : ℕ) : ZMod 269665073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2854495385411919762116496381035264358442074113 : Nat.Prime 2854495385411919762116496381035264358442074113 := by
  refine lucas_primality 2854495385411919762116496381035264358442074113 (3 : ZMod 2854495385411919762116496381035264358442074113) ?_ (fun q hq hd => ?_)
  · rw [show 2854495385411919762116496381035264358442074113 - 1 = 2854495385411919762116496381035264358442074112 from by norm_num]
    reduce_mod_char
  · have e : 2854495385411919762116496381035264358442074113 - 1 = [2 ^ 76, 7 ^ 1, 31 ^ 1, 151 ^ 1, 601 ^ 1, 1801 ^ 1, 100801 ^ 1, 10567201 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2854495385411919762116496381035264358442074113 - 1) / 2 = 1427247692705959881058248190517632179221037056 from by norm_num]
      have h2 : (3 : ZMod 2854495385411919762116496381035264358442074113) ^ 1427247692705959881058248190517632179221037056 = ((2854495385411919762116496381035264358442074112 : ℕ) : ZMod 2854495385411919762116496381035264358442074113) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2854495385411919762116496381035264358442074113 - 1) / 7 = 407785055058845680302356625862180622634582016 from by norm_num]
      have h2 : (3 : ZMod 2854495385411919762116496381035264358442074113) ^ 407785055058845680302356625862180622634582016 = ((2045160964290231152531626602718057773208763518 : ℕ) : ZMod 2854495385411919762116496381035264358442074113) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2854495385411919762116496381035264358442074113 - 1) / 31 = 92080496303610314906983754226944011562647552 from by norm_num]
      have h2 : (3 : ZMod 2854495385411919762116496381035264358442074113) ^ 92080496303610314906983754226944011562647552 = ((515034640425971417811623795755166168694396447 : ℕ) : ZMod 2854495385411919762116496381035264358442074113) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2854495385411919762116496381035264358442074113 - 1) / 151 = 18903942949747812994148982655862677870477312 from by norm_num]
      have h2 : (3 : ZMod 2854495385411919762116496381035264358442074113) ^ 18903942949747812994148982655862677870477312 = ((2535301200456458802993339301888 : ℕ) : ZMod 2854495385411919762116496381035264358442074113) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2854495385411919762116496381035264358442074113 - 1) / 601 = 4749576348439134379561558038328226885926912 from by norm_num]
      have h2 : (3 : ZMod 2854495385411919762116496381035264358442074113) ^ 4749576348439134379561558038328226885926912 = ((373543498465507219270433528323469881952016951 : ℕ) : ZMod 2854495385411919762116496381035264358442074113) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2854495385411919762116496381035264358442074113 - 1) / 1801 = 1584950241761199201619376113845232847552512 from by norm_num]
      have h2 : (3 : ZMod 2854495385411919762116496381035264358442074113) ^ 1584950241761199201619376113845232847552512 = ((1922662027856002459133296680324021353454314012 : ℕ) : ZMod 2854495385411919762116496381035264358442074113) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2854495385411919762116496381035264358442074113 - 1) / 100801 = 28318125667522343648540157151568579264512 from by norm_num]
      have h2 : (3 : ZMod 2854495385411919762116496381035264358442074113) ^ 28318125667522343648540157151568579264512 = ((529455740066537345805314609186325355414899194 : ℕ) : ZMod 2854495385411919762116496381035264358442074113) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2854495385411919762116496381035264358442074113 - 1) / 10567201 = 270127859346284769459433617382243827712 from by norm_num]
      have h2 : (3 : ZMod 2854495385411919762116496381035264358442074113) ^ 270127859346284769459433617382243827712 = ((1677472359255752356541588387500287852671901142 : ℕ) : ZMod 2854495385411919762116496381035264358442074113) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2790467761 : Nat.Prime 2790467761 := by
  refine lucas_primality 2790467761 (41 : ZMod 2790467761) ?_ (fun q hq hd => ?_)
  · rw [show 2790467761 - 1 = 2790467760 from by norm_num]
    reduce_mod_char
  · have e : 2790467761 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 103 ^ 1, 157 ^ 1, 719 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2790467761 - 1) / 2 = 1395233880 from by norm_num]
      have h2 : (41 : ZMod 2790467761) ^ 1395233880 = ((2790467760 : ℕ) : ZMod 2790467761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2790467761 - 1) / 3 = 930155920 from by norm_num]
      have h2 : (41 : ZMod 2790467761) ^ 930155920 = ((971657859 : ℕ) : ZMod 2790467761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2790467761 - 1) / 5 = 558093552 from by norm_num]
      have h2 : (41 : ZMod 2790467761) ^ 558093552 = ((1377000716 : ℕ) : ZMod 2790467761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2790467761 - 1) / 103 = 27091920 from by norm_num]
      have h2 : (41 : ZMod 2790467761) ^ 27091920 = ((665524110 : ℕ) : ZMod 2790467761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2790467761 - 1) / 157 = 17773680 from by norm_num]
      have h2 : (41 : ZMod 2790467761) ^ 17773680 = ((956468888 : ℕ) : ZMod 2790467761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2790467761 - 1) / 719 = 3881040 from by norm_num]
      have h2 : (41 : ZMod 2790467761) ^ 3881040 = ((1449084292 : ℕ) : ZMod 2790467761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_75005713 : Nat.Prime 75005713 := by
  refine lucas_primality 75005713 (5 : ZMod 75005713) ?_ (fun q hq hd => ?_)
  · rw [show 75005713 - 1 = 75005712 from by norm_num]
    reduce_mod_char
  · have e : 75005713 - 1 = [2 ^ 4, 3 ^ 2, 167 ^ 1, 3119 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75005713 - 1) / 2 = 37502856 from by norm_num]
      have h2 : (5 : ZMod 75005713) ^ 37502856 = ((75005712 : ℕ) : ZMod 75005713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75005713 - 1) / 3 = 25001904 from by norm_num]
      have h2 : (5 : ZMod 75005713) ^ 25001904 = ((57301528 : ℕ) : ZMod 75005713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75005713 - 1) / 167 = 449136 from by norm_num]
      have h2 : (5 : ZMod 75005713) ^ 449136 = ((64037274 : ℕ) : ZMod 75005713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75005713 - 1) / 3119 = 24048 from by norm_num]
      have h2 : (5 : ZMod 75005713) ^ 24048 = ((56282245 : ℕ) : ZMod 75005713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_13625405957 : Nat.Prime 13625405957 := by
  refine lucas_primality 13625405957 (3 : ZMod 13625405957) ?_ (fun q hq hd => ?_)
  · rw [show 13625405957 - 1 = 13625405956 from by norm_num]
    reduce_mod_char
  · have e : 13625405957 - 1 = [2 ^ 2, 17 ^ 1, 59 ^ 1, 67 ^ 1, 173 ^ 1, 293 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13625405957 - 1) / 2 = 6812702978 from by norm_num]
      have h2 : (3 : ZMod 13625405957) ^ 6812702978 = ((13625405956 : ℕ) : ZMod 13625405957) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13625405957 - 1) / 17 = 801494468 from by norm_num]
      have h2 : (3 : ZMod 13625405957) ^ 801494468 = ((9927647007 : ℕ) : ZMod 13625405957) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13625405957 - 1) / 59 = 230939084 from by norm_num]
      have h2 : (3 : ZMod 13625405957) ^ 230939084 = ((10137708994 : ℕ) : ZMod 13625405957) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13625405957 - 1) / 67 = 203364268 from by norm_num]
      have h2 : (3 : ZMod 13625405957) ^ 203364268 = ((2178926931 : ℕ) : ZMod 13625405957) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13625405957 - 1) / 173 = 78759572 from by norm_num]
      have h2 : (3 : ZMod 13625405957) ^ 78759572 = ((3357307503 : ℕ) : ZMod 13625405957) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13625405957 - 1) / 293 = 46503092 from by norm_num]
      have h2 : (3 : ZMod 13625405957) ^ 46503092 = ((557853116 : ℕ) : ZMod 13625405957) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_53430101 : Nat.Prime 53430101 := by
  refine lucas_primality 53430101 (2 : ZMod 53430101) ?_ (fun q hq hd => ?_)
  · rw [show 53430101 - 1 = 53430100 from by norm_num]
    reduce_mod_char
  · have e : 53430101 - 1 = [2 ^ 2, 5 ^ 2, 534301 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53430101 - 1) / 2 = 26715050 from by norm_num]
      have h2 : (2 : ZMod 53430101) ^ 26715050 = ((53430100 : ℕ) : ZMod 53430101) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53430101 - 1) / 5 = 10686020 from by norm_num]
      have h2 : (2 : ZMod 53430101) ^ 10686020 = ((50309018 : ℕ) : ZMod 53430101) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53430101 - 1) / 534301 = 100 from by norm_num]
      have h2 : (2 : ZMod 53430101) ^ 100 = ((7020504 : ℕ) : ZMod 53430101) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1068602021 : Nat.Prime 1068602021 := by
  refine lucas_primality 1068602021 (2 : ZMod 1068602021) ?_ (fun q hq hd => ?_)
  · rw [show 1068602021 - 1 = 1068602020 from by norm_num]
    reduce_mod_char
  · have e : 1068602021 - 1 = [2 ^ 2, 5 ^ 1, 53430101 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1068602021 - 1) / 2 = 534301010 from by norm_num]
      have h2 : (2 : ZMod 1068602021) ^ 534301010 = ((1068602020 : ℕ) : ZMod 1068602021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1068602021 - 1) / 5 = 213720404 from by norm_num]
      have h2 : (2 : ZMod 1068602021) ^ 213720404 = ((1018169847 : ℕ) : ZMod 1068602021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_53430101).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1068602021 - 1) / 53430101 = 20 from by norm_num]
      have h2 : (2 : ZMod 1068602021) ^ 20 = ((1048576 : ℕ) : ZMod 1068602021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_76554648784441 : Nat.Prime 76554648784441 := by
  refine lucas_primality 76554648784441 (23 : ZMod 76554648784441) ?_ (fun q hq hd => ?_)
  · rw [show 76554648784441 - 1 = 76554648784440 from by norm_num]
    reduce_mod_char
  · have e : 76554648784441 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 199 ^ 1, 1068602021 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76554648784441 - 1) / 2 = 38277324392220 from by norm_num]
      have h2 : (23 : ZMod 76554648784441) ^ 38277324392220 = ((76554648784440 : ℕ) : ZMod 76554648784441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76554648784441 - 1) / 3 = 25518216261480 from by norm_num]
      have h2 : (23 : ZMod 76554648784441) ^ 25518216261480 = ((22262988528083 : ℕ) : ZMod 76554648784441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76554648784441 - 1) / 5 = 15310929756888 from by norm_num]
      have h2 : (23 : ZMod 76554648784441) ^ 15310929756888 = ((55033704530759 : ℕ) : ZMod 76554648784441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76554648784441 - 1) / 199 = 384696727560 from by norm_num]
      have h2 : (23 : ZMod 76554648784441) ^ 384696727560 = ((24962967399833 : ℕ) : ZMod 76554648784441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1068602021).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76554648784441 - 1) / 1068602021 = 71640 from by norm_num]
      have h2 : (23 : ZMod 76554648784441) ^ 71640 = ((31576226117869 : ℕ) : ZMod 76554648784441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_38277324392221 : Nat.Prime 38277324392221 := by
  refine lucas_primality 38277324392221 (6 : ZMod 38277324392221) ?_ (fun q hq hd => ?_)
  · rw [show 38277324392221 - 1 = 38277324392220 from by norm_num]
    reduce_mod_char
  · have e : 38277324392221 - 1 = [2 ^ 2, 3 ^ 2, 5 ^ 1, 199 ^ 1, 1068602021 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38277324392221 - 1) / 2 = 19138662196110 from by norm_num]
      have h2 : (6 : ZMod 38277324392221) ^ 19138662196110 = ((38277324392220 : ℕ) : ZMod 38277324392221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38277324392221 - 1) / 3 = 12759108130740 from by norm_num]
      have h2 : (6 : ZMod 38277324392221) ^ 12759108130740 = ((14903510225242 : ℕ) : ZMod 38277324392221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38277324392221 - 1) / 5 = 7655464878444 from by norm_num]
      have h2 : (6 : ZMod 38277324392221) ^ 7655464878444 = ((10313095170315 : ℕ) : ZMod 38277324392221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38277324392221 - 1) / 199 = 192348363780 from by norm_num]
      have h2 : (6 : ZMod 38277324392221) ^ 192348363780 = ((10830148501645 : ℕ) : ZMod 38277324392221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1068602021).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38277324392221 - 1) / 1068602021 = 35820 from by norm_num]
      have h2 : (6 : ZMod 38277324392221) ^ 35820 = ((8956849557139 : ℕ) : ZMod 38277324392221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_95110361 : Nat.Prime 95110361 := by
  refine lucas_primality 95110361 (3 : ZMod 95110361) ?_ (fun q hq hd => ?_)
  · rw [show 95110361 - 1 = 95110360 from by norm_num]
    reduce_mod_char
  · have e : 95110361 - 1 = [2 ^ 3, 5 ^ 1, 59 ^ 1, 191 ^ 1, 211 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95110361 - 1) / 2 = 47555180 from by norm_num]
      have h2 : (3 : ZMod 95110361) ^ 47555180 = ((95110360 : ℕ) : ZMod 95110361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95110361 - 1) / 5 = 19022072 from by norm_num]
      have h2 : (3 : ZMod 95110361) ^ 19022072 = ((17864298 : ℕ) : ZMod 95110361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95110361 - 1) / 59 = 1612040 from by norm_num]
      have h2 : (3 : ZMod 95110361) ^ 1612040 = ((83019809 : ℕ) : ZMod 95110361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95110361 - 1) / 191 = 497960 from by norm_num]
      have h2 : (3 : ZMod 95110361) ^ 497960 = ((30589707 : ℕ) : ZMod 95110361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95110361 - 1) / 211 = 450760 from by norm_num]
      have h2 : (3 : ZMod 95110361) ^ 450760 = ((69162370 : ℕ) : ZMod 95110361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_77852679293 : Nat.Prime 77852679293 := by
  refine lucas_primality 77852679293 (3 : ZMod 77852679293) ?_ (fun q hq hd => ?_)
  · rw [show 77852679293 - 1 = 77852679292 from by norm_num]
    reduce_mod_char
  · have e : 77852679293 - 1 = [2 ^ 2, 29 ^ 1, 239 ^ 1, 839 ^ 1, 3347 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77852679293 - 1) / 2 = 38926339646 from by norm_num]
      have h2 : (3 : ZMod 77852679293) ^ 38926339646 = ((77852679292 : ℕ) : ZMod 77852679293) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77852679293 - 1) / 29 = 2684575148 from by norm_num]
      have h2 : (3 : ZMod 77852679293) ^ 2684575148 = ((202474188 : ℕ) : ZMod 77852679293) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77852679293 - 1) / 239 = 325743428 from by norm_num]
      have h2 : (3 : ZMod 77852679293) ^ 325743428 = ((30184003422 : ℕ) : ZMod 77852679293) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77852679293 - 1) / 839 = 92792228 from by norm_num]
      have h2 : (3 : ZMod 77852679293) ^ 92792228 = ((67509395057 : ℕ) : ZMod 77852679293) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77852679293 - 1) / 3347 = 23260436 from by norm_num]
      have h2 : (3 : ZMod 77852679293) ^ 23260436 = ((22785571217 : ℕ) : ZMod 77852679293) := by
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

theorem prime_111349165273 : Nat.Prime 111349165273 := by
  refine lucas_primality 111349165273 (5 : ZMod 111349165273) ?_ (fun q hq hd => ?_)
  · rw [show 111349165273 - 1 = 111349165272 from by norm_num]
    reduce_mod_char
  · have e : 111349165273 - 1 = [2 ^ 3, 3 ^ 1, 47 ^ 1, 61 ^ 1, 331 ^ 1, 4889 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111349165273 - 1) / 2 = 55674582636 from by norm_num]
      have h2 : (5 : ZMod 111349165273) ^ 55674582636 = ((111349165272 : ℕ) : ZMod 111349165273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111349165273 - 1) / 3 = 37116388424 from by norm_num]
      have h2 : (5 : ZMod 111349165273) ^ 37116388424 = ((7856549744 : ℕ) : ZMod 111349165273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111349165273 - 1) / 47 = 2369131176 from by norm_num]
      have h2 : (5 : ZMod 111349165273) ^ 2369131176 = ((38427371436 : ℕ) : ZMod 111349165273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111349165273 - 1) / 61 = 1825396152 from by norm_num]
      have h2 : (5 : ZMod 111349165273) ^ 1825396152 = ((49501409043 : ℕ) : ZMod 111349165273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111349165273 - 1) / 331 = 336402312 from by norm_num]
      have h2 : (5 : ZMod 111349165273) ^ 336402312 = ((59967842494 : ℕ) : ZMod 111349165273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111349165273 - 1) / 4889 = 22775448 from by norm_num]
      have h2 : (5 : ZMod 111349165273) ^ 22775448 = ((99894084218 : ℕ) : ZMod 111349165273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_35273039401 : Nat.Prime 35273039401 := by
  refine lucas_primality 35273039401 (7 : ZMod 35273039401) ?_ (fun q hq hd => ?_)
  · rw [show 35273039401 - 1 = 35273039400 from by norm_num]
    reduce_mod_char
  · have e : 35273039401 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 2, 47 ^ 1, 293 ^ 1, 1423 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35273039401 - 1) / 2 = 17636519700 from by norm_num]
      have h2 : (7 : ZMod 35273039401) ^ 17636519700 = ((35273039400 : ℕ) : ZMod 35273039401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35273039401 - 1) / 3 = 11757679800 from by norm_num]
      have h2 : (7 : ZMod 35273039401) ^ 11757679800 = ((1938854662 : ℕ) : ZMod 35273039401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35273039401 - 1) / 5 = 7054607880 from by norm_num]
      have h2 : (7 : ZMod 35273039401) ^ 7054607880 = ((16501366997 : ℕ) : ZMod 35273039401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35273039401 - 1) / 47 = 750490200 from by norm_num]
      have h2 : (7 : ZMod 35273039401) ^ 750490200 = ((32947296022 : ℕ) : ZMod 35273039401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35273039401 - 1) / 293 = 120385800 from by norm_num]
      have h2 : (7 : ZMod 35273039401) ^ 120385800 = ((30389128695 : ℕ) : ZMod 35273039401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35273039401 - 1) / 1423 = 24787800 from by norm_num]
      have h2 : (7 : ZMod 35273039401) ^ 24787800 = ((23232391361 : ℕ) : ZMod 35273039401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_47392381 : Nat.Prime 47392381 := by
  refine lucas_primality 47392381 (6 : ZMod 47392381) ?_ (fun q hq hd => ?_)
  · rw [show 47392381 - 1 = 47392380 from by norm_num]
    reduce_mod_char
  · have e : 47392381 - 1 = [2 ^ 2, 3 ^ 2, 5 ^ 1, 7 ^ 1, 29 ^ 1, 1297 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47392381 - 1) / 2 = 23696190 from by norm_num]
      have h2 : (6 : ZMod 47392381) ^ 23696190 = ((47392380 : ℕ) : ZMod 47392381) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47392381 - 1) / 3 = 15797460 from by norm_num]
      have h2 : (6 : ZMod 47392381) ^ 15797460 = ((38384718 : ℕ) : ZMod 47392381) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47392381 - 1) / 5 = 9478476 from by norm_num]
      have h2 : (6 : ZMod 47392381) ^ 9478476 = ((2097136 : ℕ) : ZMod 47392381) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47392381 - 1) / 7 = 6770340 from by norm_num]
      have h2 : (6 : ZMod 47392381) ^ 6770340 = ((33554176 : ℕ) : ZMod 47392381) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47392381 - 1) / 29 = 1634220 from by norm_num]
      have h2 : (6 : ZMod 47392381) ^ 1634220 = ((5715218 : ℕ) : ZMod 47392381) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47392381 - 1) / 1297 = 36540 from by norm_num]
      have h2 : (6 : ZMod 47392381) ^ 36540 = ((20910961 : ℕ) : ZMod 47392381) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 : Nat.Prime 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 := by
  refine lucas_primality 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ?_ (fun q hq hd => ?_)
  · rw [show 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1 = 3108270227561166513471139050917630250627849827446163307471742778796333223910258298060 from by norm_num]
    reduce_mod_char
  · have e : 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1 = [2 ^ 2, 3 ^ 3, 5 ^ 1, 11 ^ 1, 29 ^ 1, 31 ^ 1, 41 ^ 1, 43 ^ 1, 71 ^ 1, 113 ^ 1, 127 ^ 1, 281 ^ 1, 283 ^ 1, 86171 ^ 1, 122921 ^ 1, 1681003 ^ 1, 7416361 ^ 1, 47392381 ^ 1, 35273039401 ^ 1, 111349165273 ^ 1, 165768537521 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 2 = 1554135113780583256735569525458815125313924913723081653735871389398166611955129149030 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 1554135113780583256735569525458815125313924913723081653735871389398166611955129149030 = ((3108270227561166513471139050917630250627849827446163307471742778796333223910258298060 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 3 = 1036090075853722171157046350305876750209283275815387769157247592932111074636752766020 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 1036090075853722171157046350305876750209283275815387769157247592932111074636752766020 = ((1624295524397438571025077178355624354533850035686145030260033517028515186367929177728 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 5 = 621654045512233302694227810183526050125569965489232661494348555759266644782051659612 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 621654045512233302694227810183526050125569965489232661494348555759266644782051659612 = ((355263815384500737043037120554460572994367294553603465379477927536216340780870184812 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 11 = 282570020687378773951921731901602750057077257040560300679249343526939383991841663460 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 282570020687378773951921731901602750057077257040560300679249343526939383991841663460 = ((1455976479777143154163911357064331242899381228710736320554868536687744121017727286987 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 29 = 107181731984867810809349622445435525883718959567109079567991130303321835307250286140 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 107181731984867810809349622445435525883718959567109079567991130303321835307250286140 = ((2355454157590972419038028462352658561968470222414610509029671607537255439999609695368 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 31 = 100266781534231177853907711319923556471866123466005267982959444477301071739040590260 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 100266781534231177853907711319923556471866123466005267982959444477301071739040590260 = ((1942485816217599674589917280191030882738231027933524555643834203715927992881869450268 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 41 = 75811468964906500328564367095551957332386581157223495304188848263325200583177031660 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 75811468964906500328564367095551957332386581157223495304188848263325200583177031660 = ((3091022279103325077104154889648416831819434584881391632912097775929543921764439612463 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 43 = 72285354129329453801654396532968145363438368080143332731900994855728679625819960420 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 72285354129329453801654396532968145363438368080143332731900994855728679625819960420 = ((2821905211872529760147298395190241162770353924882902457839261308979883033757501183720 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 71 = 43778453909312204415086465505882116206026053907692440950306236321075115829721947860 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 43778453909312204415086465505882116206026053907692440950306236321075115829721947860 = ((1961946002776350008396003929748440405313659656919421332373818355980752928036519693909 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 113 = 27506816173107668260806540273607347350688936526072241659041971493772860388586356620 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 27506816173107668260806540273607347350688936526072241659041971493772860388586356620 = ((397849994001403940266928261163794960799257558427878132282697081117358118312770256429 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 127 = 24474568720954067035205819298564017721479132499576089035210573061388450581970537780 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 24474568720954067035205819298564017721479132499576089035210573061388450581970537780 = ((801500478584483985962039620577319066272940101006184229390349080947243096692424504635 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 281 = 11061459884559311435840352494368790927501244937530830275700152237709370903595225260 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 11061459884559311435840352494368790927501244937530830275700152237709370903595225260 = ((1953505115993934431062456738288735591580440801587320320521315720671774620371948197758 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 283 = 10983287023184333969862682158719541521653179602283262570571529253697290543852502820 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 10983287023184333969862682158719541521653179602283262570571529253697290543852502820 = ((13803492693581127574869511724554050904902212992580615968803948851101696 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 86171 = 36070954585198808340058013147319054561602509283241035934035148469860315232621860 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 36070954585198808340058013147319054561602509283241035934035148469860315232621860 = ((1963940984112146566317692075822464749889420664720590685522316493922513673646660928103 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 122921 = 25286730725922881472418374817302415784348075816550168868393055529944706143866860 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 25286730725922881472418374817302415784348075816550168868393055529944706143866860 = ((1499236324644780901446889108923263918629550579091605368920872583940849824244475967198 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 1681003 = 1849056918733141174329337336648197683542414753243250194956072522652448106226020 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 1849056918733141174329337336648197683542414753243250194956072522652448106226020 = ((682977388302713690273557954217138355638403291580365626765324313836596246973047284682 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 7416361 = 419109887930369963580675084575525685794940379445682769146720713675660236052460 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 419109887930369963580675084575525685794940379445682769146720713675660236052460 = ((1792288446590269228231932813821105715777270557345179609756424360735486063603454752258 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_47392381).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 47392381 = 65585863423092553916443637869083434542523825241997512373808414031705501859260 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 65585863423092553916443637869083434542523825241997512373808414031705501859260 = ((1701846883194901050544194396792679985062858396969335498234263051459623769585001898752 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_35273039401).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 35273039401 = 88120283376346814901774306299667953885714251025400693325178608948316334060 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 88120283376346814901774306299667953885714251025400693325178608948316334060 = ((2820640605379935365240639091781822494861035778042851928411456526971282570059960614724 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_111349165273).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 111349165273 = 27914625313449578206530818623873082176327935582710807875314486901051106220 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 27914625313449578206530818623873082176327935582710807875314486901051106220 = ((3034600809441094655453898181227006986447462106752176441768678731510720644796545097050 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_165768537521).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1) / 165768537521 = 18750664474960470466218411145281676968266276772289020739256225526342430860 from by norm_num]
      have h2 : (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) ^ 18750664474960470466218411145281676968266276772289020739256225526342430860 = ((1110787607507755195258444811761485688573916043954421340154106035510245438456205088607 : ℕ) : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_344759057 : Nat.Prime 344759057 := by
  refine lucas_primality 344759057 (3 : ZMod 344759057) ?_ (fun q hq hd => ?_)
  · rw [show 344759057 - 1 = 344759056 from by norm_num]
    reduce_mod_char
  · have e : 344759057 - 1 = [2 ^ 4, 101 ^ 1, 317 ^ 1, 673 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (344759057 - 1) / 2 = 172379528 from by norm_num]
      have h2 : (3 : ZMod 344759057) ^ 172379528 = ((344759056 : ℕ) : ZMod 344759057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (344759057 - 1) / 101 = 3413456 from by norm_num]
      have h2 : (3 : ZMod 344759057) ^ 3413456 = ((182517434 : ℕ) : ZMod 344759057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (344759057 - 1) / 317 = 1087568 from by norm_num]
      have h2 : (3 : ZMod 344759057) ^ 1087568 = ((306779912 : ℕ) : ZMod 344759057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (344759057 - 1) / 673 = 512272 from by norm_num]
      have h2 : (3 : ZMod 344759057) ^ 512272 = ((120555165 : ℕ) : ZMod 344759057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_141912771239 : Nat.Prime 141912771239 := by
  refine lucas_primality 141912771239 (13 : ZMod 141912771239) ?_ (fun q hq hd => ?_)
  · rw [show 141912771239 - 1 = 141912771238 from by norm_num]
    reduce_mod_char
  · have e : 141912771239 - 1 = [2 ^ 1, 7 ^ 1, 503 ^ 1, 1049 ^ 1, 19211 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (141912771239 - 1) / 2 = 70956385619 from by norm_num]
      have h2 : (13 : ZMod 141912771239) ^ 70956385619 = ((141912771238 : ℕ) : ZMod 141912771239) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (141912771239 - 1) / 7 = 20273253034 from by norm_num]
      have h2 : (13 : ZMod 141912771239) ^ 20273253034 = ((98190346359 : ℕ) : ZMod 141912771239) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (141912771239 - 1) / 503 = 282132746 from by norm_num]
      have h2 : (13 : ZMod 141912771239) ^ 282132746 = ((35033856249 : ℕ) : ZMod 141912771239) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (141912771239 - 1) / 1049 = 135283862 from by norm_num]
      have h2 : (13 : ZMod 141912771239) ^ 135283862 = ((135414587709 : ℕ) : ZMod 141912771239) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (141912771239 - 1) / 19211 = 7387058 from by norm_num]
      have h2 : (13 : ZMod 141912771239) ^ 7387058 = ((119299636697 : ℕ) : ZMod 141912771239) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_76632896469061 : Nat.Prime 76632896469061 := by
  refine lucas_primality 76632896469061 (2 : ZMod 76632896469061) ?_ (fun q hq hd => ?_)
  · rw [show 76632896469061 - 1 = 76632896469060 from by norm_num]
    reduce_mod_char
  · have e : 76632896469061 - 1 = [2 ^ 2, 3 ^ 3, 5 ^ 1, 141912771239 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76632896469061 - 1) / 2 = 38316448234530 from by norm_num]
      have h2 : (2 : ZMod 76632896469061) ^ 38316448234530 = ((76632896469060 : ℕ) : ZMod 76632896469061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76632896469061 - 1) / 3 = 25544298823020 from by norm_num]
      have h2 : (2 : ZMod 76632896469061) ^ 25544298823020 = ((41802011443591 : ℕ) : ZMod 76632896469061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76632896469061 - 1) / 5 = 15326579293812 from by norm_num]
      have h2 : (2 : ZMod 76632896469061) ^ 15326579293812 = ((75132216265291 : ℕ) : ZMod 76632896469061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_141912771239).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76632896469061 - 1) / 141912771239 = 540 from by norm_num]
      have h2 : (2 : ZMod 76632896469061) ^ 540 = ((56710046298698 : ℕ) : ZMod 76632896469061) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_541028249071570661 : Nat.Prime 541028249071570661 := by
  refine lucas_primality 541028249071570661 (10 : ZMod 541028249071570661) ?_ (fun q hq hd => ?_)
  · rw [show 541028249071570661 - 1 = 541028249071570660 from by norm_num]
    reduce_mod_char
  · have e : 541028249071570661 - 1 = [2 ^ 2, 5 ^ 1, 353 ^ 1, 76632896469061 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (541028249071570661 - 1) / 2 = 270514124535785330 from by norm_num]
      have h2 : (10 : ZMod 541028249071570661) ^ 270514124535785330 = ((541028249071570660 : ℕ) : ZMod 541028249071570661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (541028249071570661 - 1) / 5 = 108205649814314132 from by norm_num]
      have h2 : (10 : ZMod 541028249071570661) ^ 108205649814314132 = ((296987200842697098 : ℕ) : ZMod 541028249071570661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (541028249071570661 - 1) / 353 = 1532657929381220 from by norm_num]
      have h2 : (10 : ZMod 541028249071570661) ^ 1532657929381220 = ((145996249765165111 : ℕ) : ZMod 541028249071570661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_76632896469061).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (541028249071570661 - 1) / 76632896469061 = 7060 from by norm_num]
      have h2 : (10 : ZMod 541028249071570661) ^ 7060 = ((25876243252531221 : ℕ) : ZMod 541028249071570661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_130612831 : Nat.Prime 130612831 := by
  refine lucas_primality 130612831 (3 : ZMod 130612831) ?_ (fun q hq hd => ?_)
  · rw [show 130612831 - 1 = 130612830 from by norm_num]
    reduce_mod_char
  · have e : 130612831 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 4353761 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (130612831 - 1) / 2 = 65306415 from by norm_num]
      have h2 : (3 : ZMod 130612831) ^ 65306415 = ((130612830 : ℕ) : ZMod 130612831) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (130612831 - 1) / 3 = 43537610 from by norm_num]
      have h2 : (3 : ZMod 130612831) ^ 43537610 = ((126118601 : ℕ) : ZMod 130612831) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (130612831 - 1) / 5 = 26122566 from by norm_num]
      have h2 : (3 : ZMod 130612831) ^ 26122566 = ((47655585 : ℕ) : ZMod 130612831) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (130612831 - 1) / 4353761 = 30 from by norm_num]
      have h2 : (3 : ZMod 130612831) ^ 30 = ((118399123 : ℕ) : ZMod 130612831) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_92525303484856757 : Nat.Prime 92525303484856757 := by
  refine lucas_primality 92525303484856757 (3 : ZMod 92525303484856757) ?_ (fun q hq hd => ?_)
  · rw [show 92525303484856757 - 1 = 92525303484856756 from by norm_num]
    reduce_mod_char
  · have e : 92525303484856757 - 1 = [2 ^ 2, 211 ^ 1, 367 ^ 1, 2287 ^ 1, 130612831 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92525303484856757 - 1) / 2 = 46262651742428378 from by norm_num]
      have h2 : (3 : ZMod 92525303484856757) ^ 46262651742428378 = ((92525303484856756 : ℕ) : ZMod 92525303484856757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92525303484856757 - 1) / 211 = 438508547321596 from by norm_num]
      have h2 : (3 : ZMod 92525303484856757) ^ 438508547321596 = ((82134052285053308 : ℕ) : ZMod 92525303484856757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92525303484856757 - 1) / 367 = 252112543555468 from by norm_num]
      have h2 : (3 : ZMod 92525303484856757) ^ 252112543555468 = ((86076748403256595 : ℕ) : ZMod 92525303484856757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92525303484856757 - 1) / 2287 = 40457063176588 from by norm_num]
      have h2 : (3 : ZMod 92525303484856757) ^ 40457063176588 = ((3825668868341423 : ℕ) : ZMod 92525303484856757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_130612831).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92525303484856757 - 1) / 130612831 = 708393676 from by norm_num]
      have h2 : (3 : ZMod 92525303484856757) ^ 708393676 = ((31199323733936696 : ℕ) : ZMod 92525303484856757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- 2^d + 1 divides 2^m + 1 when m is an odd multiple of d.
theorem tpd {d m : ℕ} (h : m % (2 * d) = d) : 2 ^ d + 1 ∣ 2 ^ m + 1 := by
  have := one_add_pow_dvd_of_odd_mul (z := 2) h
  rwa [add_comm 1 (2 ^ d), add_comm 1 (2 ^ m)] at this

-- The left side of the balance equation holds exactly four factors of 5.
theorem budget_kernel5 {m : ℕ} {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hS : S ⊆ P) (h : 5 ^ 5 ∣ (2 ^ m + 1) * ∏ p ∈ S, (p + 1)) : False :=
  kill_v5 hP h5 E dvd_rfl hS (h.trans ⟨1 + 5 ^ 4, by ring⟩)

-- One more simple prime q with 5^i dividing q + 1 joins the 5-adic count.
theorem bud5_cons {m j i q : ℕ} {P S : Finset ℕ}
    (h : S ⊆ P ∧ 5 ^ j ∣ (2 ^ m + 1) * ∏ p ∈ S, (p + 1)) (hq : q ∈ P) (hqS : q ∉ S)
    (h3 : 5 ^ i ∣ q + 1) :
    insert q S ⊆ P ∧ 5 ^ (j + i) ∣ (2 ^ m + 1) * ∏ p ∈ insert q S, (p + 1) := by
  refine ⟨Finset.insert_subset hq h.1, ?_⟩
  rw [Finset.prod_insert hqS, pow_add]
  have e1 : (2 ^ m + 1) * ((q + 1) * ∏ p ∈ S, (p + 1)) =
      ((2 ^ m + 1) * ∏ p ∈ S, (p + 1)) * (q + 1) := by ring
  rw [e1]
  exact mul_dvd_mul h.2 h3

-- 15 divides a (a an odd multiple of 30): 7 divides 13 + 1 and 41 + 1 (2^30+1 -> 13; 2^30+1 -> 41).
theorem k_q15 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 30 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g13 : 13 ∈ P := S2 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13 ∣ 2 ^ 30 + 1).trans hd)
  have g41 : 41 ∈ P := S2 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41 ∣ 2 ^ 30 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 41 g41 (by norm_num) (by norm_num)) (by norm_num)

-- 25 divides a (a an odd multiple of 50): 3 divides 41 + 1 and 101 + 1 (2^50+1 -> 41; 2^50+1 -> 101).
theorem k_q25 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 50 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g41 : 41 ∈ P := S2 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41 ∣ 2 ^ 50 + 1).trans hd)
  have g101 : 101 ∈ P := S2 101 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 101 ∣ 2 ^ 50 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 101 g101 (by norm_num) (by norm_num)) (by norm_num)

-- 27 divides a (a an odd multiple of 54): 7 divides 13 + 1 and 139537 + 1 (2^54+1 -> 13; 2^54+1 -> 279073 -> 139537).
theorem k_q27 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 54 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g13 : 13 ∈ P := S2 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13 ∣ 2 ^ 54 + 1).trans hd)
  have g279073 : 279073 ∈ P := S2 279073 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 279073 ∣ 2 ^ 54 + 1).trans hd)
  have g139537 : 139537 ∈ P := S1 139537 (by norm_num) (by norm_num) (hnz (by norm_num)) 279073 g279073 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 139537 g139537 (by norm_num) (by norm_num)) (by norm_num)

-- 7 divides a (a an odd multiple of 14): 3 divides 29 + 1 and 113 + 1 (2^14+1 -> 29; 2^14+1 -> 113).
theorem k_q7 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 14 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g29 : 29 ∈ P := S2 29 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 29 ∣ 2 ^ 14 + 1).trans hd)
  have g113 : 113 ∈ P := S2 113 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 113 ∣ 2 ^ 14 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 113 g113 (by norm_num) (by norm_num)) (by norm_num)

-- 11 divides a (a an odd multiple of 22): 5^5 divides (2^22 + 1) * prod (p + 1) over p in {199, 19, 79} (2^22+1 -> 397 -> 199; 2^22+1 -> 2113 -> 151 -> 19; 5^4+1 -> 313 -> 157 -> 79).
theorem k_q11 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 22 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g397 : 397 ∈ P := S2 397 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 397 ∣ 2 ^ 22 + 1).trans hd)
  have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 397 g397 (by norm_num)
  have g2113 : 2113 ∈ P := S2 2113 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2113 ∣ 2 ^ 22 + 1).trans hd)
  have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 2113 g2113 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 g151 (by norm_num)
  have g313 : 313 ∈ P := S7 313 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g157 : 157 ∈ P := S1 157 (by norm_num) (by norm_num) (hnz (by norm_num)) 313 g313 (by norm_num)
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 157 g157 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 5 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by
      rw [Finset.prod_empty, mul_one]
      exact ((dvd_of_eq (by norm_num : 5 ^ 1 = 5)).trans (by norm_num : 5 ∣ 2 ^ 22 + 1)).trans hd⟩
  have b1 := bud5_cons b0 g199 (by simp) (by norm_num : 5 ^ 2 ∣ 199 + 1)
  have b2 := bud5_cons b1 g19 (by simp) (by norm_num : 5 ^ 1 ∣ 19 + 1)
  have b3 := bud5_cons b2 g79 (by simp) (by norm_num : 5 ^ 1 ∣ 79 + 1)
  exact budget_kernel5 hP h5 E b3.1 ((pow_dvd_pow 5 (by norm_num)).trans b3.2)

-- 13 divides a (a an odd multiple of 26): 3^2 divides 53 + 1 (2^26+1 -> 53).
theorem k_q13 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 26 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g53 : 53 ∈ P := S2 53 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 53 ∣ 2 ^ 26 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 53 g53 (by norm_num)

-- 17 divides a (a an odd multiple of 34): 3^2 divides 953 + 1 (2^34+1 -> 953).
theorem k_q17 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 34 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g953 : 953 ∈ P := S2 953 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 953 ∣ 2 ^ 34 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 953 g953 (by norm_num)

-- 19 divides a (a an odd multiple of 38): 229 divides 2^38 + 1 and 457 + 1 (2^38+1 -> 457).
theorem k_q19 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 38 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g457 : 457 ∈ P := S2 457 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 457 ∣ 2 ^ 38 + 1).trans hd)
  exact S4 229 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 229 ∣ 2 ^ 38 + 1).trans hd) 457 g457 (by norm_num)

-- 23 divides a (a an odd multiple of 46): 13^2 divides 1013 + 1 (2^46+1 -> 1013).
theorem k_q23 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 46 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g1013 : 1013 ∈ P := S2 1013 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1013 ∣ 2 ^ 46 + 1).trans hd)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1013 g1013 (by norm_num)

-- 29 divides a (a an odd multiple of 58): 7^2 divides 536903681 + 1 (2^58+1 -> 536903681).
theorem k_q29 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 58 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g536903681 : 536903681 ∈ P := S2 536903681 prime_536903681 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 536903681 ∣ 2 ^ 58 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 536903681 g536903681 (by norm_num)

-- 31 divides a (a an odd multiple of 62): 3 divides 8681 + 1 and 384773 + 1 (2^62+1 -> 8681; 2^62+1 -> 384773).
theorem k_q31 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 62 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g8681 : 8681 ∈ P := S2 8681 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8681 ∣ 2 ^ 62 + 1).trans hd)
  have g384773 : 384773 ∈ P := S2 384773 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 384773 ∣ 2 ^ 62 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 8681 g8681 384773 g384773 (by norm_num) (by norm_num)) (by norm_num)

-- 37 divides a (a an odd multiple of 74): 3^2 divides 593 + 1 (2^74+1 -> 593).
theorem k_q37 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 74 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g593 : 593 ∈ P := S2 593 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 593 ∣ 2 ^ 74 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 593 g593 (by norm_num)

-- 41 divides a (a an odd multiple of 82): 3^2 divides 10169 + 1 (2^82+1 -> 10169).
theorem k_q41 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 82 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g10169 : 10169 ∈ P := S2 10169 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 10169 ∣ 2 ^ 82 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 10169 g10169 (by norm_num)

-- 43 divides a (a an odd multiple of 86): 3 divides 173 + 1 and 500177 + 1 (2^86+1 -> 173; 2^86+1 -> 500177).
theorem k_q43 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 86 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g173 : 173 ∈ P := S2 173 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 173 ∣ 2 ^ 86 + 1).trans hd)
  have g500177 : 500177 ∈ P := S2 500177 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 500177 ∣ 2 ^ 86 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 173 g173 500177 g500177 (by norm_num) (by norm_num)) (by norm_num)

-- 47 divides a (a an odd multiple of 94): 3^2 divides 3761 + 1 (2^94+1 -> 3761).
theorem k_q47 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 94 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g3761 : 3761 ∈ P := S2 3761 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3761 ∣ 2 ^ 94 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 3761 g3761 (by norm_num)

-- 53 divides a (a an odd multiple of 106): 3^2 divides 1535813 + 1 (2^106+1 -> 15358129 -> 1535813).
theorem k_q53 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 106 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g15358129 : 15358129 ∈ P := S2 15358129 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 15358129 ∣ 2 ^ 106 + 1).trans hd)
  have g1535813 : 1535813 ∈ P := S1 1535813 (by norm_num) (by norm_num) (hnz (by norm_num)) 15358129 g15358129 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1535813 g1535813 (by norm_num)

-- 59 divides a (a an odd multiple of 118): 3 divides 1181 + 1 and 157649 + 1 (2^118+1 -> 1181; 2^118+1 -> 157649).
theorem k_q59 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 118 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g1181 : 1181 ∈ P := S2 1181 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1181 ∣ 2 ^ 118 + 1).trans hd)
  have g157649 : 157649 ∈ P := S2 157649 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 157649 ∣ 2 ^ 118 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1181 g1181 157649 g157649 (by norm_num) (by norm_num)) (by norm_num)

-- 61 divides a (a an odd multiple of 122): 3^2 divides 1709 + 1 (2^122+1 -> 1709).
theorem k_q61 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 122 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g1709 : 1709 ∈ P := S2 1709 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1709 ∣ 2 ^ 122 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1709 g1709 (by norm_num)

-- 67 divides a (a an odd multiple of 134): 3^2 divides 269 + 1 (2^134+1 -> 269).
theorem k_q67 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 134 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g269 : 269 ∈ P := S2 269 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 269 ∣ 2 ^ 134 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 269 g269 (by norm_num)

-- 71 divides a (a an odd multiple of 142): 3^2 divides 4999465853 + 1 (2^142+1 -> 4999465853).
theorem k_q71 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 142 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g4999465853 : 4999465853 ∈ P := S2 4999465853 prime_4999465853 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4999465853 ∣ 2 ^ 142 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 4999465853 g4999465853 (by norm_num)

-- 73 divides a (a an odd multiple of 146): 7^2 divides 293 + 1 (2^146+1 -> 293).
theorem k_q73 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 146 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g293 : 293 ∈ P := S2 293 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 293 ∣ 2 ^ 146 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 293 g293 (by norm_num)

-- 79 divides a (a an odd multiple of 158): 3^2 divides 53 + 1 (2^158+1 -> 317 -> 53).
theorem k_q79 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 158 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g317 : 317 ∈ P := S2 317 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 317 ∣ 2 ^ 158 + 1).trans hd)
  have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 317 g317 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 53 g53 (by norm_num)

-- 83 divides a (a an odd multiple of 166): 7 divides 6531769 + 1 and 2029 + 1 (2^166+1 -> 13063537 -> 6531769; 2^166+1 -> 13063537 -> 6531769 -> 4057 -> 2029).
theorem k_q83 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 166 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g13063537 : 13063537 ∈ P := S2 13063537 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13063537 ∣ 2 ^ 166 + 1).trans hd)
  have g6531769 : 6531769 ∈ P := S1 6531769 (by norm_num) (by norm_num) (hnz (by norm_num)) 13063537 g13063537 (by norm_num)
  have g4057 : 4057 ∈ P := S1 4057 (by norm_num) (by norm_num) (hnz (by norm_num)) 6531769 g6531769 (by norm_num)
  have g2029 : 2029 ∈ P := S1 2029 (by norm_num) (by norm_num) (hnz (by norm_num)) 4057 g4057 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 6531769 g6531769 2029 g2029 (by norm_num) (by norm_num)) (by norm_num)

-- 89 divides a (a an odd multiple of 178): 3^2 divides 107 + 1 (2^178+1 -> 1069 -> 107).
theorem k_q89 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 178 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g1069 : 1069 ∈ P := S2 1069 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1069 ∣ 2 ^ 178 + 1).trans hd)
  have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (hnz (by norm_num)) 1069 g1069 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 107 g107 (by norm_num)

-- 97 divides a (a an odd multiple of 194): 3 divides 389 + 1 and 3881 + 1 (2^194+1 -> 389; 2^194+1 -> 3881).
theorem k_q97 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 194 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g389 : 389 ∈ P := S2 389 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 389 ∣ 2 ^ 194 + 1).trans hd)
  have g3881 : 3881 ∈ P := S2 3881 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3881 ∣ 2 ^ 194 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 3881 g3881 (by norm_num) (by norm_num)) (by norm_num)

-- 101 divides a (a an odd multiple of 202): 3^2 divides 809 + 1 (2^202+1 -> 809).
theorem k_q101 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 202 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g809 : 809 ∈ P := S2 809 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 809 ∣ 2 ^ 202 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 809 g809 (by norm_num)

-- 103 divides a (a an odd multiple of 206): 3^2 divides 41201 + 1 (2^206+1 -> 41201).
theorem k_q103 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 206 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g41201 : 41201 ∈ P := S2 41201 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41201 ∣ 2 ^ 206 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 41201 g41201 (by norm_num)

-- 107 divides a (a an odd multiple of 214): 11 divides 857 + 1 and 843589 + 1 (2^214+1 -> 857; 2^214+1 -> 843589).
theorem k_q107 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 214 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g857 : 857 ∈ P := S2 857 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 857 ∣ 2 ^ 214 + 1).trans hd)
  have g843589 : 843589 ∈ P := S2 843589 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 843589 ∣ 2 ^ 214 + 1).trans hd)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 857 g857 843589 g843589 (by norm_num) (by norm_num)) (by norm_num)

-- 109 divides a (a an odd multiple of 218): 3^2 divides 5669 + 1 (2^218+1 -> 5669).
theorem k_q109 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 218 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g5669 : 5669 ∈ P := S2 5669 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5669 ∣ 2 ^ 218 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 5669 g5669 (by norm_num)

-- 113 divides a (a an odd multiple of 226): 7^2 divides 58309 + 1 (2^226+1 -> 58309).
theorem k_q113 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 226 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g58309 : 58309 ∈ P := S2 58309 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 58309 ∣ 2 ^ 226 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 58309 g58309 (by norm_num)

-- 127 divides a (a an odd multiple of 254): 3 divides 509 + 1 and 18797 + 1 (2^254+1 -> 509; 2^254+1 -> 18797).
theorem k_q127 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 254 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g509 : 509 ∈ P := S2 509 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 509 ∣ 2 ^ 254 + 1).trans hd)
  have g18797 : 18797 ∈ P := S2 18797 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 18797 ∣ 2 ^ 254 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 509 g509 18797 g18797 (by norm_num) (by norm_num)) (by norm_num)

-- 131 divides a (a an odd multiple of 262): 3^2 divides 269665073 + 1 (2^262+1 -> 269665073).
theorem k_q131 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 262 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g269665073 : 269665073 ∈ P := S2 269665073 prime_269665073 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 269665073 ∣ 2 ^ 262 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 269665073 g269665073 (by norm_num)

-- 137 divides a (a an odd multiple of 274): 3^2 divides 23633 + 1 (2^274+1 -> 189061 -> 94531 -> 23633).
theorem k_q137 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 274 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g189061 : 189061 ∈ P := S2 189061 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 189061 ∣ 2 ^ 274 + 1).trans hd)
  have g94531 : 94531 ∈ P := S1 94531 (by norm_num) (by norm_num) (hnz (by norm_num)) 189061 g189061 (by norm_num)
  have g23633 : 23633 ∈ P := S1 23633 (by norm_num) (by norm_num) (hnz (by norm_num)) 94531 g94531 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 23633 g23633 (by norm_num)

-- 139 divides a (a an odd multiple of 278): 3^2 divides 557 + 1 (2^278+1 -> 557).
theorem k_q139 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 278 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g557 : 557 ∈ P := S2 557 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 557 ∣ 2 ^ 278 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 557 g557 (by norm_num)

-- 149 divides a (a an odd multiple of 298): 3^2 divides 179 + 1 (2^298+1 -> 1789 -> 179).
theorem k_q149 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 298 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g1789 : 1789 ∈ P := S2 1789 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 1789 ∣ 2 ^ 298 + 1).trans hd)
  have g179 : 179 ∈ P := S1 179 (by norm_num) (by norm_num) (hnz (by norm_num)) 1789 g1789 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 179 g179 (by norm_num)

-- 151 divides a (a an odd multiple of 302): 11^2 divides 67759 + 1 (2^302+1 -> 2854495385411919762116496381035264358442074113 -> 18837001 -> 67759).
theorem k_q151 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 302 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g2854495385411919762116496381035264358442074113 : 2854495385411919762116496381035264358442074113 ∈ P := S2 2854495385411919762116496381035264358442074113 prime_2854495385411919762116496381035264358442074113 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 2854495385411919762116496381035264358442074113 ∣ 2 ^ 302 + 1).trans hd)
  have g18837001 : 18837001 ∈ P := S1 18837001 (by norm_num) (by norm_num) (hnz (by norm_num)) 2854495385411919762116496381035264358442074113 g2854495385411919762116496381035264358442074113 (by norm_num)
  have g67759 : 67759 ∈ P := S1 67759 (by norm_num) (by norm_num) (hnz (by norm_num)) 18837001 g18837001 (by norm_num)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 67759 g67759 (by norm_num)

-- 157 divides a (a an odd multiple of 314): 3^2 divides 1493 + 1 (2^314+1 -> 2790467761 -> 1493).
theorem k_q157 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 314 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g2790467761 : 2790467761 ∈ P := S2 2790467761 prime_2790467761 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 2790467761 ∣ 2 ^ 314 + 1).trans hd)
  have g1493 : 1493 ∈ P := S1 1493 (by norm_num) (by norm_num) (hnz (by norm_num)) 2790467761 g2790467761 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1493 g1493 (by norm_num)

-- 163 divides a (a an odd multiple of 326): 3^2 divides 7807049 + 1 (2^326+1 -> 7807049).
theorem k_q163 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 326 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g7807049 : 7807049 ∈ P := S2 7807049 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 7807049 ∣ 2 ^ 326 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 7807049 g7807049 (by norm_num)

-- 167 divides a (a an odd multiple of 334): 3^2 divides 232937 + 1 (2^334+1 -> 75005713 -> 232937).
theorem k_q167 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 334 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g75005713 : 75005713 ∈ P := S2 75005713 prime_75005713 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 75005713 ∣ 2 ^ 334 + 1).trans hd)
  have g232937 : 232937 ∈ P := S1 232937 (by norm_num) (by norm_num) (hnz (by norm_num)) 75005713 g75005713 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 232937 g232937 (by norm_num)

-- 173 divides a (a an odd multiple of 346): 3 divides 13625405957 + 1 and 11 + 1 (2^346+1 -> 13625405957; 2^346+1 -> 13625405957 -> 43 -> 11).
theorem k_q173 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 346 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g13625405957 : 13625405957 ∈ P := S2 13625405957 prime_13625405957 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 13625405957 ∣ 2 ^ 346 + 1).trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 13625405957 g13625405957 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 13625405957 g13625405957 11 g11 (by norm_num) (by norm_num)) (by norm_num)

-- 179 divides a (a an odd multiple of 358): 3^2 divides 39869 + 1 (2^358+1 -> 31815461 -> 39869).
theorem k_q179 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 358 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g31815461 : 31815461 ∈ P := S2 31815461 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 31815461 ∣ 2 ^ 358 + 1).trans hd)
  have g39869 : 39869 ∈ P := S1 39869 (by norm_num) (by norm_num) (hnz (by norm_num)) 31815461 g31815461 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 39869 g39869 (by norm_num)

-- 181 divides a (a an odd multiple of 362): 3^2 divides 9413 + 1 (2^362+1 -> 9413).
theorem k_q181 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 362 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g9413 : 9413 ∈ P := S2 9413 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 9413 ∣ 2 ^ 362 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 9413 g9413 (by norm_num)

-- 191 divides a (a an odd multiple of 382): 7^2 divides 3821 + 1 (2^382+1 -> 3821).
theorem k_q191 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 382 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g3821 : 3821 ∈ P := S2 3821 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 3821 ∣ 2 ^ 382 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 3821 g3821 (by norm_num)

-- 193 divides a (a an odd multiple of 386): 3^2 divides 773 + 1 (2^386+1 -> 773).
theorem k_q193 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 386 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g773 : 773 ∈ P := S2 773 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 773 ∣ 2 ^ 386 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 773 g773 (by norm_num)

-- 197 divides a (a an odd multiple of 394): 11 divides 4729 + 1 and 43 + 1 (2^394+1 -> 4729; 2^394+1 -> 4729 -> 43).
theorem k_q197 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 394 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g4729 : 4729 ∈ P := S2 4729 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 4729 ∣ 2 ^ 394 + 1).trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 4729 g4729 (by norm_num)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 4729 g4729 43 g43 (by norm_num) (by norm_num)) (by norm_num)

-- 199 divides a (a an odd multiple of 398): 3^2 divides 3761 + 1 (2^398+1 -> 76554648784441 -> 38277324392221 -> 3761).
theorem k_q199 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 398 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g76554648784441 : 76554648784441 ∈ P := S2 76554648784441 prime_76554648784441 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 76554648784441 ∣ 2 ^ 398 + 1).trans hd)
  have g38277324392221 : 38277324392221 ∈ P := S1 38277324392221 prime_38277324392221 (by norm_num) (hnz (by norm_num)) 76554648784441 g76554648784441 (by norm_num)
  have g3761 : 3761 ∈ P := S1 3761 (by norm_num) (by norm_num) (hnz (by norm_num)) 38277324392221 g38277324392221 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 3761 g3761 (by norm_num)

-- 211 divides a (a an odd multiple of 422): 3^2 divides 95110361 + 1 (2^422+1 -> 95110361).
theorem k_q211 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 422 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g95110361 : 95110361 ∈ P := S2 95110361 prime_95110361 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 95110361 ∣ 2 ^ 422 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 95110361 g95110361 (by norm_num)

-- 223 divides a (a an odd multiple of 446): 3 divides 11597 + 1 and 6530333 + 1 (2^446+1 -> 11597; 2^446+1 -> 6530333).
theorem k_q223 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 446 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g11597 : 11597 ∈ P := S2 11597 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 11597 ∣ 2 ^ 446 + 1).trans hd)
  have g6530333 : 6530333 ∈ P := S2 6530333 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 6530333 ∣ 2 ^ 446 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 11597 g11597 6530333 g6530333 (by norm_num) (by norm_num)) (by norm_num)

-- 227 divides a (a an odd multiple of 454): 5^5 divides (2^454 + 1) * prod (p + 1) over p in {5449, 109, 79} (2^454+1 -> 5449; 2^454+1 -> 5449 -> 109; 5^4+1 -> 313 -> 157 -> 79).
theorem k_q227 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 454 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g5449 : 5449 ∈ P := S2 5449 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 5449 ∣ 2 ^ 454 + 1).trans hd)
  have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 5449 g5449 (by norm_num)
  have g313 : 313 ∈ P := S7 313 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g157 : 157 ∈ P := S1 157 (by norm_num) (by norm_num) (hnz (by norm_num)) 313 g313 (by norm_num)
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 157 g157 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 5 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by
      rw [Finset.prod_empty, mul_one]
      exact ((dvd_of_eq (by norm_num : 5 ^ 1 = 5)).trans (by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 5 ∣ 2 ^ 454 + 1)).trans hd⟩
  have b1 := bud5_cons b0 g5449 (by simp) (by norm_num : 5 ^ 2 ∣ 5449 + 1)
  have b2 := bud5_cons b1 g109 (by simp) (by norm_num : 5 ^ 1 ∣ 109 + 1)
  have b3 := bud5_cons b2 g79 (by simp) (by norm_num : 5 ^ 1 ∣ 79 + 1)
  exact budget_kernel5 hP h5 E b3.1 ((pow_dvd_pow 5 (by norm_num)).trans b3.2)

-- 229 divides a (a an odd multiple of 458): 11 divides 2749 + 1 and 131 + 1 (2^458+1 -> 2749; 2^458+1 -> 5523481 -> 2761741 -> 131).
theorem k_q229 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 458 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g2749 : 2749 ∈ P := S2 2749 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 2749 ∣ 2 ^ 458 + 1).trans hd)
  have g5523481 : 5523481 ∈ P := S2 5523481 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 5523481 ∣ 2 ^ 458 + 1).trans hd)
  have g2761741 : 2761741 ∈ P := S1 2761741 (by norm_num) (by norm_num) (hnz (by norm_num)) 5523481 g5523481 (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 2761741 g2761741 (by norm_num)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 2749 g2749 131 g131 (by norm_num) (by norm_num)) (by norm_num)

-- 233 divides a (a an odd multiple of 466): 13^2 divides 30757 + 1 (2^466+1 -> 30757).
theorem k_q233 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 466 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g30757 : 30757 ∈ P := S2 30757 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 30757 ∣ 2 ^ 466 + 1).trans hd)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 30757 g30757 (by norm_num)

-- 239 divides a (a an odd multiple of 478): 3^2 divides 5171561 + 1 (2^478+1 -> 77852679293 -> 5171561).
theorem k_q239 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 478 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g77852679293 : 77852679293 ∈ P := S2 77852679293 prime_77852679293 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 77852679293 ∣ 2 ^ 478 + 1).trans hd)
  have g5171561 : 5171561 ∈ P := S1 5171561 (by norm_num) (by norm_num) (hnz (by norm_num)) 77852679293 g77852679293 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 5171561 g5171561 (by norm_num)

-- 241 divides a (a an odd multiple of 482): 3^2 divides 251 + 1 (2^482+1 -> 15594629 -> 251).
theorem k_q241 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 482 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g15594629 : 15594629 ∈ P := S2 15594629 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 15594629 ∣ 2 ^ 482 + 1).trans hd)
  have g251 : 251 ∈ P := S1 251 (by norm_num) (by norm_num) (hnz (by norm_num)) 15594629 g15594629 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 251 g251 (by norm_num)

-- 251 divides a (a an odd multiple of 502): 3^2 divides 5021 + 1 (2^502+1 -> 5021).
theorem k_q251 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 502 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g5021 : 5021 ∈ P := S2 5021 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 5021 ∣ 2 ^ 502 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 5021 g5021 (by norm_num)

-- 257 divides a (a an odd multiple of 514): 3^2 divides 71 + 1 (2^514+1 -> 28564009 -> 71).
theorem k_q257 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 514 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g28564009 : 28564009 ∈ P := S2 28564009 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 28564009 ∣ 2 ^ 514 + 1).trans hd)
  have g71 : 71 ∈ P := S1 71 (by norm_num) (by norm_num) (hnz (by norm_num)) 28564009 g28564009 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 71 g71 (by norm_num)

-- 263 divides a (a an odd multiple of 526): 3^2 divides 731141 + 1 (2^526+1 -> 731141).
theorem k_q263 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 526 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g731141 : 731141 ∈ P := S2 731141 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 731141 ∣ 2 ^ 526 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 731141 g731141 (by norm_num)

-- 269 divides a (a an odd multiple of 538): 3^2 divides 5381 + 1 (2^538+1 -> 5381).
theorem k_q269 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 538 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g5381 : 5381 ∈ P := S2 5381 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 5381 ∣ 2 ^ 538 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 5381 g5381 (by norm_num)

-- 271 divides a (a an odd multiple of 542): 3^2 divides 1309337 + 1 (2^542+1 -> 10474693 -> 5237347 -> 1309337).
theorem k_q271 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 542 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g10474693 : 10474693 ∈ P := S2 10474693 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 10474693 ∣ 2 ^ 542 + 1).trans hd)
  have g5237347 : 5237347 ∈ P := S1 5237347 (by norm_num) (by norm_num) (hnz (by norm_num)) 10474693 g10474693 (by norm_num)
  have g1309337 : 1309337 ∈ P := S1 1309337 (by norm_num) (by norm_num) (hnz (by norm_num)) 5237347 g5237347 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1309337 g1309337 (by norm_num)

-- 277 divides a (a an odd multiple of 554): 3^2 divides 14543 + 1 (2^554+1 -> 232681 -> 116341 -> 58171 -> 14543).
theorem k_q277 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 554 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g232681 : 232681 ∈ P := S2 232681 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 232681 ∣ 2 ^ 554 + 1).trans hd)
  have g116341 : 116341 ∈ P := S1 116341 (by norm_num) (by norm_num) (hnz (by norm_num)) 232681 g232681 (by norm_num)
  have g58171 : 58171 ∈ P := S1 58171 (by norm_num) (by norm_num) (hnz (by norm_num)) 116341 g116341 (by norm_num)
  have g14543 : 14543 ∈ P := S1 14543 (by norm_num) (by norm_num) (hnz (by norm_num)) 58171 g58171 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 14543 g14543 (by norm_num)

-- 281 divides a (a an odd multiple of 562): 7 divides 3373 + 1 and 3827221 + 1 (2^562+1 -> 3373; 2^562+1 -> 3827221).
theorem k_q281 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 562 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g3373 : 3373 ∈ P := S2 3373 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 3373 ∣ 2 ^ 562 + 1).trans hd)
  have g3827221 : 3827221 ∈ P := S2 3827221 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 3827221 ∣ 2 ^ 562 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 3373 g3373 3827221 g3827221 (by norm_num) (by norm_num)) (by norm_num)

-- 283 divides a (a an odd multiple of 566): 3^2 divides 449 + 1 (2^566+1 -> 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 -> 449).
theorem k_q283 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 566 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 : 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 ∈ P := S2 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 prime_3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 ∣ 2 ^ 566 + 1).trans hd)
  have g449 : 449 ∈ P := S1 449 (by norm_num) (by norm_num) (hnz (by norm_num)) 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 g3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 449 g449 (by norm_num)

-- 293 divides a (a an odd multiple of 586): 17^2 divides 22396921 + 1 (2^586+1 -> 22396921).
theorem k_q293 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 586 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g22396921 : 22396921 ∈ P := S2 22396921 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 22396921 ∣ 2 ^ 586 + 1).trans hd)
  exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 22396921 g22396921 (by norm_num)

-- 307 divides a (a an odd multiple of 614): 3^2 divides 93329 + 1 (2^614+1 -> 93329).
theorem k_q307 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 614 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g93329 : 93329 ∈ P := S2 93329 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 93329 ∣ 2 ^ 614 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 93329 g93329 (by norm_num)

-- 311 divides a (a an odd multiple of 622): 3^2 divides 21149 + 1 (2^622+1 -> 21149).
theorem k_q311 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 622 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g21149 : 21149 ∈ P := S2 21149 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 21149 ∣ 2 ^ 622 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 21149 g21149 (by norm_num)

-- 313 divides a (a an odd multiple of 626): 3^2 divides 42569 + 1 (2^626+1 -> 42569).
theorem k_q313 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 626 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g42569 : 42569 ∈ P := S2 42569 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 42569 ∣ 2 ^ 626 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 42569 g42569 (by norm_num)

-- 317 divides a (a an odd multiple of 634): 3^2 divides 344759057 + 1 (2^634+1 -> 344759057).
theorem k_q317 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 634 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g344759057 : 344759057 ∈ P := S2 344759057 prime_344759057 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 344759057 ∣ 2 ^ 634 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 344759057 g344759057 (by norm_num)

-- 331 divides a (a an odd multiple of 662): 3 divides 589181 + 1 and 11 + 1 (2^662+1 -> 589181; 2^662+1 -> 589181 -> 11).
theorem k_q331 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 662 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g589181 : 589181 ∈ P := S2 589181 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 589181 ∣ 2 ^ 662 + 1).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 589181 g589181 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 589181 g589181 11 g11 (by norm_num) (by norm_num)) (by norm_num)

-- 337 divides a (a an odd multiple of 674): 3^2 divides 2549069 + 1 (2^674+1 -> 2549069).
theorem k_q337 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 674 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g2549069 : 2549069 ∈ P := S2 2549069 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 2549069 ∣ 2 ^ 674 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 2549069 g2549069 (by norm_num)

-- 347 divides a (a an odd multiple of 694): 29 divides 5575597 + 1 and 463 + 1 (2^694+1 -> 5575597; 2^694+1 -> 2777 -> 463).
theorem k_q347 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 694 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g5575597 : 5575597 ∈ P := S2 5575597 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 5575597 ∣ 2 ^ 694 + 1).trans hd)
  have g2777 : 2777 ∈ P := S2 2777 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 2777 ∣ 2 ^ 694 + 1).trans hd)
  have g463 : 463 ∈ P := S1 463 (by norm_num) (by norm_num) (hnz (by norm_num)) 2777 g2777 (by norm_num)
  exact absurd (S3 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 5575597 g5575597 463 g463 (by norm_num) (by norm_num)) (by norm_num)

-- 349 divides a (a an odd multiple of 698): 3^2 divides 763613 + 1 (2^698+1 -> 763613).
theorem k_q349 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 698 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g763613 : 763613 ∈ P := S2 763613 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 763613 ∣ 2 ^ 698 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 763613 g763613 (by norm_num)

-- 353 divides a (a an odd multiple of 706): 3 divides 541028249071570661 + 1 and 83 + 1 (2^706+1 -> 541028249071570661; 2^706+1 -> 541028249071570661 -> 83).
theorem k_q353 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 706 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g541028249071570661 : 541028249071570661 ∈ P := S2 541028249071570661 prime_541028249071570661 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 541028249071570661 ∣ 2 ^ 706 + 1).trans hd)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 541028249071570661 g541028249071570661 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 541028249071570661 g541028249071570661 83 g83 (by norm_num) (by norm_num)) (by norm_num)

-- 359 divides a (a an odd multiple of 718): 3 divides 41 + 1 and 29 + 1 (2^718+1 -> 585889 -> 41; 2^718+1 -> 5199757 -> 29).
theorem k_q359 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 718 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g585889 : 585889 ∈ P := S2 585889 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 585889 ∣ 2 ^ 718 + 1).trans hd)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 585889 g585889 (by norm_num)
  have g5199757 : 5199757 ∈ P := S2 5199757 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 5199757 ∣ 2 ^ 718 + 1).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 5199757 g5199757 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 29 g29 (by norm_num) (by norm_num)) (by norm_num)

-- 367 divides a (a an odd multiple of 734): 3 divides 92525303484856757 + 1 and 18767603 + 1 (2^734+1 -> 92525303484856757; 2^734+1 -> 92525303484856757 -> 18767603).
theorem k_q367 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 734 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g92525303484856757 : 92525303484856757 ∈ P := S2 92525303484856757 prime_92525303484856757 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 92525303484856757 ∣ 2 ^ 734 + 1).trans hd)
  have g18767603 : 18767603 ∈ P := S1 18767603 (by norm_num) (by norm_num) (hnz (by norm_num)) 92525303484856757 g92525303484856757 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 92525303484856757 g92525303484856757 18767603 g18767603 (by norm_num) (by norm_num)) (by norm_num)

-- 373 divides a (a an odd multiple of 746): 3^2 divides 1493 + 1 (2^746+1 -> 1493).
theorem k_q373 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 746 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g1493 : 1493 ∈ P := S2 1493 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 1493 ∣ 2 ^ 746 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1493 g1493 (by norm_num)

-- 379 divides a (a an odd multiple of 758): 7 divides 4549 + 1 and 13 + 1 (2^758+1 -> 4549; 2^758+1 -> 4549 -> 13).
theorem k_q379 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 758 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g4549 : 4549 ∈ P := S2 4549 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 4549 ∣ 2 ^ 758 + 1).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 4549 g4549 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 4549 g4549 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- 383 divides a (a an odd multiple of 766): 11^2 divides 4597 + 1 (2^766+1 -> 4597).
theorem k_q383 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 766 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g4597 : 4597 ∈ P := S2 4597 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 4597 ∣ 2 ^ 766 + 1).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 4597 g4597 (by norm_num)

-- 389 divides a (a an odd multiple of 778): 3^2 divides 17117 + 1 (2^778+1 -> 17117).
theorem k_q389 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 778 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g17117 : 17117 ∈ P := S2 17117 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 17117 ∣ 2 ^ 778 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 17117 g17117 (by norm_num)

-- 397 divides a (a an odd multiple of 794): 11^2 divides 25409 + 1 (2^794+1 -> 25409).
theorem k_q397 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 794 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g25409 : 25409 ∈ P := S2 25409 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 25409 ∣ 2 ^ 794 + 1).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 25409 g25409 (by norm_num)

-- 401 divides a (a an odd multiple of 802): 3^2 divides 107 + 1 (2^802+1 -> 3209 -> 107).
theorem k_q401 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 802 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g3209 : 3209 ∈ P := S2 3209 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 3209 ∣ 2 ^ 802 + 1).trans hd)
  have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (hnz (by norm_num)) 3209 g3209 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 107 g107 (by norm_num)

-- 409 divides a (a an odd multiple of 818): 3^2 divides 1637 + 1 (2^818+1 -> 1637).
theorem k_q409 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 818 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g1637 : 1637 ∈ P := S2 1637 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 1637 ∣ 2 ^ 818 + 1).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1637 g1637 (by norm_num)

-- 419 divides a (a an odd multiple of 838): 3 divides 53633 + 1 and 63689 + 1 (2^838+1 -> 53633; 2^838+1 -> 63689).
theorem k_q419 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hd : 2 ^ 838 + 1 ∣ 2 ^ m + 1) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 4) E
  have g53633 : 53633 ∈ P := S2 53633 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 53633 ∣ 2 ^ 838 + 1).trans hd)
  have g63689 : 63689 ∈ P := S2 63689 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 63689 ∣ 2 ^ 838 + 1).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 53633 g53633 63689 g63689 (by norm_num) (by norm_num)) (by norm_num)

-- a = 2 mod 4: no prime q with 7 <= q <= 420 divides a, and 15, 25, 27 do not divide a.
theorem sieve {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (h4 : m % 4 = 2) :
    (∀ q, q.Prime → 7 ≤ q → q ≤ 420 → ¬ q ∣ m) ∧
    ¬ 15 ∣ m ∧ ¬ 25 ∣ m ∧ ¬ 27 ∣ m := by
  have D : ∀ q : ℕ, q % 2 = 1 → q ∣ m → 2 ^ (2 * q) + 1 ∣ 2 ^ m + 1 :=
    fun q hq hd => tpd (mod_of_dvd_two_mod_four hd hq h4)
  refine ⟨?_, fun hd => k_q15 hP E (D 15 (by norm_num) hd), fun hd => k_q25 hP E (D 25 (by norm_num) hd),
    fun hd => k_q27 hP E (D 27 (by norm_num) hd)⟩
  intro q hq lo hi hd
  interval_cases q
  · exact k_q7 hP E (D 7 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q11 hP h5 E (D 11 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q13 hP E (D 13 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q17 hP E (D 17 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q19 hP E (D 19 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q23 hP E (D 23 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q29 hP E (D 29 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q31 hP E (D 31 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q37 hP E (D 37 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q41 hP E (D 41 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q43 hP E (D 43 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q47 hP E (D 47 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q53 hP E (D 53 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q59 hP E (D 59 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q61 hP E (D 61 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q67 hP E (D 67 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q71 hP E (D 71 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q73 hP E (D 73 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q79 hP E (D 79 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q83 hP E (D 83 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q89 hP E (D 89 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q97 hP E (D 97 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q101 hP E (D 101 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q103 hP E (D 103 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q107 hP E (D 107 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q109 hP E (D 109 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q113 hP E (D 113 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q127 hP E (D 127 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q131 hP E (D 131 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q137 hP E (D 137 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q139 hP E (D 139 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q149 hP E (D 149 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q151 hP E (D 151 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q157 hP E (D 157 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q163 hP E (D 163 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q167 hP E (D 167 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q173 hP E (D 173 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q179 hP E (D 179 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q181 hP E (D 181 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q191 hP E (D 191 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q193 hP E (D 193 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q197 hP E (D 197 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q199 hP E (D 199 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q211 hP E (D 211 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q223 hP E (D 223 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q227 hP h5 E (D 227 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q229 hP E (D 229 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q233 hP E (D 233 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q239 hP E (D 239 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q241 hP E (D 241 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q251 hP E (D 251 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q257 hP E (D 257 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q263 hP E (D 263 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q269 hP E (D 269 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q271 hP E (D 271 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q277 hP E (D 277 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q281 hP E (D 281 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q283 hP E (D 283 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q293 hP E (D 293 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q307 hP E (D 307 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q311 hP E (D 311 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q313 hP E (D 313 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q317 hP E (D 317 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q331 hP E (D 331 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q337 hP E (D 337 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q347 hP E (D 347 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact k_q349 hP E (D 349 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q353 hP E (D 353 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q359 hP E (D 359 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q367 hP E (D 367 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q373 hP E (D 373 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q379 hP E (D 379 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q383 hP E (D 383 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q389 hP E (D 389 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q397 hP E (D 397 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q401 hP E (D 401 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q409 hP E (D 409 (by norm_num) hd)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact k_q419 hP E (D 419 (by norm_num) hd)
  · exact absurd hq (by norm_num)

-- Section 2. The classes of a.

-- Pure arithmetic: a multiple of 2^r is an odd multiple of 2^r or a multiple of 2^(r+1).
theorem splitp {m r : ℕ} (h : m % 2 ^ r = 0) : m % 2 ^ (r + 1) = 2 ^ r ∨ m % 2 ^ (r + 1) = 0 := by
  obtain ⟨t, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  have hk : 0 < 2 ^ r := Nat.pos_of_ne_zero (by positivity)
  rw [pow_succ]
  rcases Nat.even_or_odd' t with ⟨s, rfl | rfl⟩
  · right
    rw [show 2 ^ r * (2 * s) = 2 ^ r * 2 * s from by ring]
    exact Nat.mul_mod_right _ _
  · left
    rw [show 2 ^ r * (2 * s + 1) = 2 ^ r * 2 * s + 2 ^ r from by ring, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)

theorem dblp {m r : ℕ} (h : m % 2 ^ r = 0) (h2 : m % 2 ^ (r + 1) ≠ 2 ^ r) : m % 2 ^ (r + 1) = 0 :=
  (splitp h).resolve_left h2

-- The classes left by the parent: a even and v2(a) not in R5 means v2(a) = 1, 20, 24 or >= 33.
theorem classes {m : ℕ} (he : Even m)
    (hR : ∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      m % 2 ^ (r + 1) ≠ 2 ^ r) :
    m % 4 = 2 ∨ m % 2 ^ 21 = 2 ^ 20 ∨ m % 2 ^ 25 = 2 ^ 24 ∨ m % 2 ^ 33 = 0 := by
  have c1 : m % 2 ^ 1 = 0 := by
    rw [pow_one]
    exact Nat.even_iff.mp he
  rcases splitp c1 with h | c
  · exact Or.inl h
  have c2 : m % 2 ^ 2 = 0 := c
  have c3 : m % 2 ^ 3 = 0 := dblp c2 (hR 2 (by simp))
  have c4 : m % 2 ^ 4 = 0 := dblp c3 (hR 3 (by simp))
  have c5 : m % 2 ^ 5 = 0 := dblp c4 (hR 4 (by simp))
  have c6 : m % 2 ^ 6 = 0 := dblp c5 (hR 5 (by simp))
  have c7 : m % 2 ^ 7 = 0 := dblp c6 (hR 6 (by simp))
  have c8 : m % 2 ^ 8 = 0 := dblp c7 (hR 7 (by simp))
  have c9 : m % 2 ^ 9 = 0 := dblp c8 (hR 8 (by simp))
  have c10 : m % 2 ^ 10 = 0 := dblp c9 (hR 9 (by simp))
  have c11 : m % 2 ^ 11 = 0 := dblp c10 (hR 10 (by simp))
  have c12 : m % 2 ^ 12 = 0 := dblp c11 (hR 11 (by simp))
  have c13 : m % 2 ^ 13 = 0 := dblp c12 (hR 12 (by simp))
  have c14 : m % 2 ^ 14 = 0 := dblp c13 (hR 13 (by simp))
  have c15 : m % 2 ^ 15 = 0 := dblp c14 (hR 14 (by simp))
  have c16 : m % 2 ^ 16 = 0 := dblp c15 (hR 15 (by simp))
  have c17 : m % 2 ^ 17 = 0 := dblp c16 (hR 16 (by simp))
  have c18 : m % 2 ^ 18 = 0 := dblp c17 (hR 17 (by simp))
  have c19 : m % 2 ^ 19 = 0 := dblp c18 (hR 18 (by simp))
  have c20 : m % 2 ^ 20 = 0 := dblp c19 (hR 19 (by simp))
  rcases splitp c20 with h | c
  · exact Or.inr (Or.inl h)
  have c21 : m % 2 ^ 21 = 0 := c
  have c22 : m % 2 ^ 22 = 0 := dblp c21 (hR 21 (by simp))
  have c23 : m % 2 ^ 23 = 0 := dblp c22 (hR 22 (by simp))
  have c24 : m % 2 ^ 24 = 0 := dblp c23 (hR 23 (by simp))
  rcases splitp c24 with h | c
  · exact Or.inr (Or.inr (Or.inl h))
  have c25 : m % 2 ^ 25 = 0 := c
  have c26 : m % 2 ^ 26 = 0 := dblp c25 (hR 25 (by simp))
  have c27 : m % 2 ^ 27 = 0 := dblp c26 (hR 26 (by simp))
  have c28 : m % 2 ^ 28 = 0 := dblp c27 (hR 27 (by simp))
  have c29 : m % 2 ^ 29 = 0 := dblp c28 (hR 28 (by simp))
  have c30 : m % 2 ^ 30 = 0 := dblp c29 (hR 29 (by simp))
  have c31 : m % 2 ^ 31 = 0 := dblp c30 (hR 30 (by simp))
  have c32 : m % 2 ^ 32 = 0 := dblp c31 (hR 31 (by simp))
  have c33 : m % 2 ^ 33 = 0 := dblp c32 (hR 32 (by simp))
  exact Or.inr (Or.inr (Or.inr c33))

-- The step.
theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩ ⟨A4, h4⟩
  refine ⟨max A1 (max A2 (max A3 A4)), fun n h hS he hev hbig hR => ?_⟩
  obtain ⟨hP, h5, E⟩ := setup h hS
  rw [he] at E
  rcases classes hev hR with c | c | c | c
  · obtain ⟨s1, s2, s3, s4⟩ := sieve hP h5 E c
    exact (h1 n h hS he c hbig s1 s2 s3 s4).trans (le_max_left _ _)
  · exact (h2 n h hS he c).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h3 n h hS he c).trans
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  · exact (h4 n h hS he c).trans
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1
