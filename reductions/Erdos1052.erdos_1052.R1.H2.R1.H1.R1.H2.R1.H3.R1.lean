import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H3.R1
-- Upstream path: reductions/Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H3.R1.lean
-- Credit: @adammcarter (agent: Claude Code, model claude-fable-5-2)
--
-- Splits step H3 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1 (5 is the only repeated odd prime of
-- the unitary perfect number n, e = v5(n) >= 41, with the parent's conditions on e and on
-- a = padicValNat 2 n) by the parity of e, after sieving the exponent e up to 283.
-- Proving H1 and H2 proves the step.
--
-- Notation as in the parent file: P = the set of simple odd primes of n.  The balance equation is
--   (2^a + 1)(1 + 5^e) prod_P (p + 1) = 2^(a+1) 5^e prod_P p,
-- in which every odd prime other than 5 occurs exactly once on the left.  If e is an odd multiple
-- of d then 1 + 5^d divides 1 + 5^e, so the odd primes of 1 + 5^d are simple primes of n, and the
-- odd primes (other than 5) of p + 1 for simple p are simple again.
--
-- PROVED BELOW (no hypothesis needed):
--  * odd_divisor_mod_six: if d is odd and e is an odd multiple of d then d = 1 mod 6.  (3 divides
--    1 + 5^d; for d = 3 mod 6 so does 9; for d = 5 mod 6 the number (1 + 5^d)/6 is 2 mod 3, so it
--    has a prime r = 2 mod 3, and then 3 divides both 1 + 5^e and r + 1.)  So for odd e every
--    divisor of e is 1 mod 6.
--  * not_odd_odd: a and e are not both odd (3 would divide both 2^a + 1 and 1 + 5^e).
--  * odd_two_divisor_mod_six: if a is odd then every divisor of a is 1 mod 6 (same argument with
--    2^d + 1 in place of 1 + 5^d).
--  * esieve: e is no odd multiple of any d with 3 <= d <= 283, d != 4.  Each d is settled by the
--    mod 6 lemma (106 values), by a class of the parent chain (106), by an earlier d (1), or by
--    its own lemma ke<d> (67 values): a chain of forced simple primes starting at primes of
--    1 + 5^d that ends at a prime with two sources on the left (30 cases) or at a square
--    dividing some p + 1 (37 cases).  Primes above 4.3 * 10^7 carry a Lucas certificate (theorems
--    prime_<p>, 89 new, up to 185 digits).
--    In particular no e with 41 <= e <= 283 is possible, so e > 283.
-- The classes d = 1, 2, 4 cannot be sieved this way: their forced primes ({3}, {13, 7},
-- {313, 157, 79}) are consistent, and d = 4 is the exponent of Wall's unitary perfect number
-- 2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313.
--
-- H1 (OPEN): e > 283 odd.  Then every divisor of e is 1 mod 6, e has no divisor d with
--   3 <= d <= 283 (so every prime factor of e exceeds 283), and a is even.
-- H2 (OPEN): e > 283 even.  Then e is no odd multiple of any d with 3 <= d <= 283, d != 4, and if a
--   is odd then every divisor of a is 1 mod 6.
-- Each H keeps every condition of the parent step (those not listed follow from the listed ones).
-- No known unitary perfect number satisfies the hypotheses of either H.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H3_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main

-- H1: a is bounded when e > 283 is odd, every divisor of e is 1 mod 6, e has no divisor d with
-- 3 <= d <= 283, a is even and v2(a) is not in R5.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → 283 < n.factorization 5 →
    Odd (n.factorization 5) →
    (∀ d, d ∣ n.factorization 5 → d % 6 = 1) →
    (∀ d, 3 ≤ d → d ≤ 283 → ¬ d ∣ n.factorization 5) →
    Even (padicValNat 2 n) →
    (∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- H2: a is bounded when e > 283 is even, e is no odd multiple of any d with 3 <= d <= 283, d != 4,
-- every divisor of a is 1 mod 6 when a is odd, a mod 14 is not 7 and v2(a) is not in R5.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → 283 < n.factorization 5 →
    Even (n.factorization 5) →
    (∀ d, 3 ≤ d → d ≤ 283 → d ≠ 4 → n.factorization 5 % (2 * d) ≠ d) →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1) →
    padicValNat 2 n % 14 ≠ 7 →
    (∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- Section 1. Uniform lemmas.

theorem odd_of_dvd_odd {d m : ℕ} (hd : d ∣ m) (hm : m % 2 = 1) : d % 2 = 1 := by
  obtain ⟨k, rfl⟩ := hd
  rcases Nat.even_or_odd d with ⟨j, rfl⟩ | h
  · exfalso
    have : (j + j) * k = 2 * (j * k) := by ring
    omega
  · exact Nat.odd_iff.mp h

-- 2^d + 1 divides 2^m + 1 when m is an odd multiple of d.
theorem tpd {d m : ℕ} (h : m % (2 * d) = d) : 2 ^ d + 1 ∣ 2 ^ m + 1 := by
  have := one_add_pow_dvd_of_odd_mul (z := 2) h
  rwa [add_comm 1 (2 ^ d), add_comm 1 (2 ^ m)] at this

-- If d is odd and 1 + 5^d divides 1 + 5^e then d = 1 mod 6.
theorem odd_divisor_mod_six {m e d : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (ho : d % 2 = 1) (hd : 1 + 5 ^ d ∣ 1 + 5 ^ e) : d % 6 = 1 := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  obtain ⟨Q, hQ, hQm⟩ := exists_quot_mod (z := 5) (Nat.odd_iff.mpr ho)
  have hQ6 : Q % 6 = d % 6 := hQm
  have h3K : 3 ∣ 1 + 5 ^ e := Dvd.dvd.trans ⟨2 * Q, by rw [hQ]; ring⟩ hd
  by_contra hne
  have hcase : d % 6 = 3 ∨ d % 6 = 5 := by omega
  rcases hcase with h3 | h5
  · obtain ⟨t, ht⟩ : 3 ∣ Q := Nat.dvd_of_mod_eq_zero (by omega)
    have h9 : 3 * 3 ∣ 1 + 5 ^ e := Dvd.dvd.trans ⟨2 * t, by rw [hQ, ht]; ring⟩ hd
    exact S_sq hP (hK5 e) E (c := 3) Nat.prime_three (by norm_num) (hnz (by norm_num))
      ((h9.mul_left _).mul_right _)
  · have hQ3 : Q % 3 = 2 := by omega
    obtain ⟨r, hrp, hrd, hr3⟩ := exists_prime_mod3 Q hQ3
    have hrd' : r ∣ 1 + 5 ^ d := by rw [hQ]; exact hrd.mul_left _
    have hr2 : r ≠ 2 := by
      rintro rfl
      omega
    have hr5 : r ≠ 5 := by
      rintro rfl
      have h1 : 5 ∣ 5 ^ d := dvd_pow_self 5 (by omega)
      have h11 : 5 ∣ 1 := (Nat.dvd_add_left h1).mp hrd'
      omega
    have hrP : r ∈ P := S7 r hrp hr2 (hnz hr5) (hrd'.trans hd)
    exact S8 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) h3K r hrP (by omega)

-- a and e are not both odd: 3 would divide both 2^a + 1 and 1 + 5^e.
theorem not_odd_odd {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hm : m % 2 = 1) (he : e % 2 = 1) : False := by
  have h3 : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one hm
  obtain ⟨Q, hQ, -⟩ := exists_quot_mod (z := 5) (Nat.odd_iff.mpr he)
  have h3K : 3 ∣ 1 + 5 ^ e := ⟨2 * Q, by rw [hQ]; ring⟩
  refine kill_sq hP E h3 (Finset.empty_subset P) Nat.prime_three (by norm_num) (by norm_num) ?_
  rw [Finset.prod_empty, mul_one]
  exact mul_dvd_mul_left 3 h3K

-- If a is odd then every divisor of a is 1 mod 6.
theorem odd_two_divisor_mod_six {m e d : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hm : m % 2 = 1) (hd : d ∣ m) : d % 6 = 1 := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have ho : d % 2 = 1 := odd_of_dvd_odd hd hm
  have hdm : 2 ^ d + 1 ∣ 2 ^ m + 1 := tpd (mod_of_dvd_odd hd hm)
  obtain ⟨Q, hQ, hQm⟩ := exists_quot_mod (z := 2) (Nat.odd_iff.mpr ho)
  have hQ3' : Q % 3 = d % 3 := hQm
  have h3 : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one hm
  by_contra hne
  have hcase : d % 6 = 3 ∨ d % 6 = 5 := by omega
  rcases hcase with h3' | h5
  · obtain ⟨t, ht⟩ : 3 ∣ Q := Nat.dvd_of_mod_eq_zero (by omega)
    exact S5 3 Nat.prime_three (by norm_num) (hnz (by norm_num))
      (Dvd.dvd.trans ⟨t, by rw [add_comm, hQ, ht]; ring⟩ hdm)
  · have hQ3 : Q % 3 = 2 := by omega
    obtain ⟨r, hrp, hrd, hr3⟩ := exists_prime_mod3 Q hQ3
    have hrd' : r ∣ 2 ^ d + 1 := by rw [add_comm, hQ]; exact hrd.mul_left _
    have hr2 : r ≠ 2 := by
      rintro rfl
      have h1 : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
      have h11 : 2 ∣ 1 := (Nat.dvd_add_right h1).mp hrd'
      omega
    have hr5 : r ≠ 5 := by
      rintro rfl
      exact five_not_dvd_of_odd ho hrd'
    have hrP : r ∈ P := S2 r hrp hr2 (hnz hr5) (hrd'.trans hdm)
    exact S4 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) h3 r hrP (by omega)

-- Section 2. Lucas certificates, the forced-chain lemmas and the exponent sieve.

-- e an odd multiple of 43: 3 divides 5^43 + 1 and 11 + 1 (5^43+1 -> 9547 -> 11).
theorem ke43 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 43 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g9547 : 9547 ∈ P := S7 9547 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 9547 ∣ 1 + 5 ^ 43).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 9547 g9547 (by norm_num)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 43).trans hd) 11 g11 (by norm_num)

theorem prime_632133361 : Nat.Prime 632133361 := by
  refine lucas_primality 632133361 (13 : ZMod 632133361) ?_ (fun q hq hd => ?_)
  · rw [show 632133361 - 1 = 632133360 from by norm_num]
    reduce_mod_char
  · have e : 632133361 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 1, 241 ^ 1, 3643 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (632133361 - 1) / 2 = 316066680 from by norm_num]
      have h2 : (13 : ZMod 632133361) ^ 316066680 = ((632133360 : ℕ) : ZMod 632133361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (632133361 - 1) / 3 = 210711120 from by norm_num]
      have h2 : (13 : ZMod 632133361) ^ 210711120 = ((511173199 : ℕ) : ZMod 632133361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (632133361 - 1) / 5 = 126426672 from by norm_num]
      have h2 : (13 : ZMod 632133361) ^ 126426672 = ((632132736 : ℕ) : ZMod 632133361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (632133361 - 1) / 241 = 2622960 from by norm_num]
      have h2 : (13 : ZMod 632133361) ^ 2622960 = ((360846791 : ℕ) : ZMod 632133361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (632133361 - 1) / 3643 = 173520 from by norm_num]
      have h2 : (13 : ZMod 632133361) ^ 173520 = ((270061633 : ℕ) : ZMod 632133361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9080418348371887359375390001 : Nat.Prime 9080418348371887359375390001 := by
  refine lucas_primality 9080418348371887359375390001 (23 : ZMod 9080418348371887359375390001) ?_ (fun q hq hd => ?_)
  · rw [show 9080418348371887359375390001 - 1 = 9080418348371887359375390000 from by norm_num]
    reduce_mod_char
  · have e : 9080418348371887359375390001 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 4, 11 ^ 1, 13 ^ 1, 41 ^ 1, 71 ^ 1, 241 ^ 1, 521 ^ 1, 9161 ^ 1, 632133361 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9080418348371887359375390001 - 1) / 2 = 4540209174185943679687695000 from by norm_num]
      have h2 : (23 : ZMod 9080418348371887359375390001) ^ 4540209174185943679687695000 = ((9080418348371887359375390000 : ℕ) : ZMod 9080418348371887359375390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9080418348371887359375390001 - 1) / 3 = 3026806116123962453125130000 from by norm_num]
      have h2 : (23 : ZMod 9080418348371887359375390001) ^ 3026806116123962453125130000 = ((6611958923523907708732022703 : ℕ) : ZMod 9080418348371887359375390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9080418348371887359375390001 - 1) / 5 = 1816083669674377471875078000 from by norm_num]
      have h2 : (23 : ZMod 9080418348371887359375390001) ^ 1816083669674377471875078000 = ((8185868234744869092119698410 : ℕ) : ZMod 9080418348371887359375390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9080418348371887359375390001 - 1) / 11 = 825492577124717032670490000 from by norm_num]
      have h2 : (23 : ZMod 9080418348371887359375390001) ^ 825492577124717032670490000 = ((9080418311118984374756249376 : ℕ) : ZMod 9080418348371887359375390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9080418348371887359375390001 - 1) / 13 = 698493719105529796875030000 from by norm_num]
      have h2 : (23 : ZMod 9080418348371887359375390001) ^ 698493719105529796875030000 = ((536674343447051320926656442 : ℕ) : ZMod 9080418348371887359375390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9080418348371887359375390001 - 1) / 41 = 221473618252972862423790000 from by norm_num]
      have h2 : (23 : ZMod 9080418348371887359375390001) ^ 221473618252972862423790000 = ((8200543328238810579948856153 : ℕ) : ZMod 9080418348371887359375390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9080418348371887359375390001 - 1) / 71 = 127893216174251934639090000 from by norm_num]
      have h2 : (23 : ZMod 9080418348371887359375390001) ^ 127893216174251934639090000 = ((7588588427361167258240643869 : ℕ) : ZMod 9080418348371887359375390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9080418348371887359375390001 - 1) / 241 = 37678084433078370785790000 from by norm_num]
      have h2 : (23 : ZMod 9080418348371887359375390001) ^ 37678084433078370785790000 = ((4118150330713845106055685377 : ℕ) : ZMod 9080418348371887359375390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9080418348371887359375390001 - 1) / 521 = 17428826004552566908590000 from by norm_num]
      have h2 : (23 : ZMod 9080418348371887359375390001) ^ 17428826004552566908590000 = ((1231163475562309440732409884 : ℕ) : ZMod 9080418348371887359375390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9080418348371887359375390001 - 1) / 9161 = 991203836739644946990000 from by norm_num]
      have h2 : (23 : ZMod 9080418348371887359375390001) ^ 991203836739644946990000 = ((1850337016603693215788851403 : ℕ) : ZMod 9080418348371887359375390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_632133361).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9080418348371887359375390001 - 1) / 632133361 = 14364719390868990000 from by norm_num]
      have h2 : (23 : ZMod 9080418348371887359375390001) ^ 14364719390868990000 = ((7599543437876891743629815003 : ℕ) : ZMod 9080418348371887359375390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4540209174185943679687695001 : Nat.Prime 4540209174185943679687695001 := by
  refine lucas_primality 4540209174185943679687695001 (35 : ZMod 4540209174185943679687695001) ?_ (fun q hq hd => ?_)
  · rw [show 4540209174185943679687695001 - 1 = 4540209174185943679687695000 from by norm_num]
    reduce_mod_char
  · have e : 4540209174185943679687695001 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 4, 11 ^ 1, 13 ^ 1, 41 ^ 1, 71 ^ 1, 241 ^ 1, 521 ^ 1, 9161 ^ 1, 632133361 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4540209174185943679687695001 - 1) / 2 = 2270104587092971839843847500 from by norm_num]
      have h2 : (35 : ZMod 4540209174185943679687695001) ^ 2270104587092971839843847500 = ((4540209174185943679687695000 : ℕ) : ZMod 4540209174185943679687695001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4540209174185943679687695001 - 1) / 3 = 1513403058061981226562565000 from by norm_num]
      have h2 : (35 : ZMod 4540209174185943679687695001) ^ 1513403058061981226562565000 = ((1013230352606762383029582285 : ℕ) : ZMod 4540209174185943679687695001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4540209174185943679687695001 - 1) / 5 = 908041834837188735937539000 from by norm_num]
      have h2 : (35 : ZMod 4540209174185943679687695001) ^ 908041834837188735937539000 = ((3106324159112018310266958393 : ℕ) : ZMod 4540209174185943679687695001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4540209174185943679687695001 - 1) / 11 = 412746288562358516335245000 from by norm_num]
      have h2 : (35 : ZMod 4540209174185943679687695001) ^ 412746288562358516335245000 = ((2364054458617143138544373028 : ℕ) : ZMod 4540209174185943679687695001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4540209174185943679687695001 - 1) / 13 = 349246859552764898437515000 from by norm_num]
      have h2 : (35 : ZMod 4540209174185943679687695001) ^ 349246859552764898437515000 = ((2992392910903933917073879379 : ℕ) : ZMod 4540209174185943679687695001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4540209174185943679687695001 - 1) / 41 = 110736809126486431211895000 from by norm_num]
      have h2 : (35 : ZMod 4540209174185943679687695001) ^ 110736809126486431211895000 = ((1792394411973874421534131257 : ℕ) : ZMod 4540209174185943679687695001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4540209174185943679687695001 - 1) / 71 = 63946608087125967319545000 from by norm_num]
      have h2 : (35 : ZMod 4540209174185943679687695001) ^ 63946608087125967319545000 = ((4199859805790761617023154612 : ℕ) : ZMod 4540209174185943679687695001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4540209174185943679687695001 - 1) / 241 = 18839042216539185392895000 from by norm_num]
      have h2 : (35 : ZMod 4540209174185943679687695001) ^ 18839042216539185392895000 = ((1545339836338493140011346619 : ℕ) : ZMod 4540209174185943679687695001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4540209174185943679687695001 - 1) / 521 = 8714413002276283454295000 from by norm_num]
      have h2 : (35 : ZMod 4540209174185943679687695001) ^ 8714413002276283454295000 = ((599706148898250892591590938 : ℕ) : ZMod 4540209174185943679687695001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4540209174185943679687695001 - 1) / 9161 = 495601918369822473495000 from by norm_num]
      have h2 : (35 : ZMod 4540209174185943679687695001) ^ 495601918369822473495000 = ((1702481766962358311013089831 : ℕ) : ZMod 4540209174185943679687695001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_632133361).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4540209174185943679687695001 - 1) / 632133361 = 7182359695434495000 from by norm_num]
      have h2 : (35 : ZMod 4540209174185943679687695001) ^ 7182359695434495000 = ((3611503553013236812668226327 : ℕ) : ZMod 4540209174185943679687695001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_31199796233 : Nat.Prime 31199796233 := by
  refine lucas_primality 31199796233 (3 : ZMod 31199796233) ?_ (fun q hq hd => ?_)
  · rw [show 31199796233 - 1 = 31199796232 from by norm_num]
    reduce_mod_char
  · have e : 31199796233 - 1 = [2 ^ 3, 11 ^ 1, 37 ^ 1, 9582247 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31199796233 - 1) / 2 = 15599898116 from by norm_num]
      have h2 : (3 : ZMod 31199796233) ^ 15599898116 = ((31199796232 : ℕ) : ZMod 31199796233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31199796233 - 1) / 11 = 2836345112 from by norm_num]
      have h2 : (3 : ZMod 31199796233) ^ 2836345112 = ((9175418380 : ℕ) : ZMod 31199796233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31199796233 - 1) / 37 = 843237736 from by norm_num]
      have h2 : (3 : ZMod 31199796233) ^ 843237736 = ((13226490397 : ℕ) : ZMod 31199796233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31199796233 - 1) / 9582247 = 3256 from by norm_num]
      have h2 : (3 : ZMod 31199796233) ^ 3256 = ((13750517610 : ℕ) : ZMod 31199796233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 44: 3^2 divides 31199796233 + 1 (5^44+1 -> 9080418348371887359375390001 -> 4540209174185943679687695001 -> 31199796233).
theorem ke44 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 44 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g9080418348371887359375390001 : 9080418348371887359375390001 ∈ P := S7 9080418348371887359375390001 prime_9080418348371887359375390001 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 9080418348371887359375390001 ∣ 1 + 5 ^ 44).trans hd)
  have g4540209174185943679687695001 : 4540209174185943679687695001 ∈ P := S1 4540209174185943679687695001 prime_4540209174185943679687695001 (by norm_num) (hnz (by norm_num)) 9080418348371887359375390001 g9080418348371887359375390001 (by norm_num)
  have g31199796233 : 31199796233 ∈ P := S1 31199796233 prime_31199796233 (by norm_num) (hnz (by norm_num)) 4540209174185943679687695001 g4540209174185943679687695001 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 31199796233 g31199796233 (by norm_num)

theorem prime_225159733 : Nat.Prime 225159733 := by
  refine lucas_primality 225159733 (2 : ZMod 225159733) ?_ (fun q hq hd => ?_)
  · rw [show 225159733 - 1 = 225159732 from by norm_num]
    reduce_mod_char
  · have e : 225159733 - 1 = [2 ^ 2, 3 ^ 2, 7 ^ 1, 113 ^ 1, 7907 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (225159733 - 1) / 2 = 112579866 from by norm_num]
      have h2 : (2 : ZMod 225159733) ^ 112579866 = ((225159732 : ℕ) : ZMod 225159733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (225159733 - 1) / 3 = 75053244 from by norm_num]
      have h2 : (2 : ZMod 225159733) ^ 75053244 = ((50284755 : ℕ) : ZMod 225159733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (225159733 - 1) / 7 = 32165676 from by norm_num]
      have h2 : (2 : ZMod 225159733) ^ 32165676 = ((125509176 : ℕ) : ZMod 225159733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (225159733 - 1) / 113 = 1992564 from by norm_num]
      have h2 : (2 : ZMod 225159733) ^ 1992564 = ((7623993 : ℕ) : ZMod 225159733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (225159733 - 1) / 7907 = 28476 from by norm_num]
      have h2 : (2 : ZMod 225159733) ^ 28476 = ((27366948 : ℕ) : ZMod 225159733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1030330938209 : Nat.Prime 1030330938209 := by
  refine lucas_primality 1030330938209 (3 : ZMod 1030330938209) ?_ (fun q hq hd => ?_)
  · rw [show 1030330938209 - 1 = 1030330938208 from by norm_num]
    reduce_mod_char
  · have e : 1030330938209 - 1 = [2 ^ 5, 11 ^ 1, 13 ^ 1, 225159733 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1030330938209 - 1) / 2 = 515165469104 from by norm_num]
      have h2 : (3 : ZMod 1030330938209) ^ 515165469104 = ((1030330938208 : ℕ) : ZMod 1030330938209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1030330938209 - 1) / 11 = 93666448928 from by norm_num]
      have h2 : (3 : ZMod 1030330938209) ^ 93666448928 = ((576985325397 : ℕ) : ZMod 1030330938209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1030330938209 - 1) / 13 = 79256226016 from by norm_num]
      have h2 : (3 : ZMod 1030330938209) ^ 79256226016 = ((187370759667 : ℕ) : ZMod 1030330938209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_225159733).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1030330938209 - 1) / 225159733 = 4576 from by norm_num]
      have h2 : (3 : ZMod 1030330938209) ^ 4576 = ((969492665400 : ℕ) : ZMod 1030330938209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5465713352000770660547109750601 : Nat.Prime 5465713352000770660547109750601 := by
  refine lucas_primality 5465713352000770660547109750601 (11 : ZMod 5465713352000770660547109750601) ?_ (fun q hq hd => ?_)
  · rw [show 5465713352000770660547109750601 - 1 = 5465713352000770660547109750600 from by norm_num]
    reduce_mod_char
  · have e : 5465713352000770660547109750601 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 2, 23 ^ 1, 67 ^ 1, 89 ^ 1, 5281 ^ 1, 12207031 ^ 1, 1030330938209 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5465713352000770660547109750601 - 1) / 2 = 2732856676000385330273554875300 from by norm_num]
      have h2 : (11 : ZMod 5465713352000770660547109750601) ^ 2732856676000385330273554875300 = ((5465713352000770660547109750600 : ℕ) : ZMod 5465713352000770660547109750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5465713352000770660547109750601 - 1) / 3 = 1821904450666923553515703250200 from by norm_num]
      have h2 : (11 : ZMod 5465713352000770660547109750601) ^ 1821904450666923553515703250200 = ((718549370350498045366279537732 : ℕ) : ZMod 5465713352000770660547109750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5465713352000770660547109750601 - 1) / 5 = 1093142670400154132109421950120 from by norm_num]
      have h2 : (11 : ZMod 5465713352000770660547109750601) ^ 1093142670400154132109421950120 = ((409091668584481571778068887203 : ℕ) : ZMod 5465713352000770660547109750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5465713352000770660547109750601 - 1) / 23 = 237639710956555246110743902200 from by norm_num]
      have h2 : (11 : ZMod 5465713352000770660547109750601) ^ 237639710956555246110743902200 = ((244140625 : ℕ) : ZMod 5465713352000770660547109750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5465713352000770660547109750601 - 1) / 67 = 81577811223892099411150891800 from by norm_num]
      have h2 : (11 : ZMod 5465713352000770660547109750601) ^ 81577811223892099411150891800 = ((4573892788249229541277813986346 : ℕ) : ZMod 5465713352000770660547109750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5465713352000770660547109750601 - 1) / 89 = 61412509573042366972439435400 from by norm_num]
      have h2 : (11 : ZMod 5465713352000770660547109750601) ^ 61412509573042366972439435400 = ((1306648433622735581889619265811 : ℕ) : ZMod 5465713352000770660547109750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5465713352000770660547109750601 - 1) / 5281 = 1034976964968901848238422600 from by norm_num]
      have h2 : (11 : ZMod 5465713352000770660547109750601) ^ 1034976964968901848238422600 = ((2498569527830377618727145424847 : ℕ) : ZMod 5465713352000770660547109750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5465713352000770660547109750601 - 1) / 12207031 = 447751246965848670372600 from by norm_num]
      have h2 : (11 : ZMod 5465713352000770660547109750601) ^ 447751246965848670372600 = ((3860921626843417376453889772266 : ℕ) : ZMod 5465713352000770660547109750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1030330938209).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5465713352000770660547109750601 - 1) / 1030330938209 = 5304813385009763400 from by norm_num]
      have h2 : (11 : ZMod 5465713352000770660547109750601) ^ 5304813385009763400 = ((4198274474402883515378283925308 : ℕ) : ZMod 5465713352000770660547109750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2732856676000385330273554875301 : Nat.Prime 2732856676000385330273554875301 := by
  refine lucas_primality 2732856676000385330273554875301 (2 : ZMod 2732856676000385330273554875301) ?_ (fun q hq hd => ?_)
  · rw [show 2732856676000385330273554875301 - 1 = 2732856676000385330273554875300 from by norm_num]
    reduce_mod_char
  · have e : 2732856676000385330273554875301 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 2, 23 ^ 1, 67 ^ 1, 89 ^ 1, 5281 ^ 1, 12207031 ^ 1, 1030330938209 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2732856676000385330273554875301 - 1) / 2 = 1366428338000192665136777437650 from by norm_num]
      have h2 : (2 : ZMod 2732856676000385330273554875301) ^ 1366428338000192665136777437650 = ((2732856676000385330273554875300 : ℕ) : ZMod 2732856676000385330273554875301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2732856676000385330273554875301 - 1) / 3 = 910952225333461776757851625100 from by norm_num]
      have h2 : (2 : ZMod 2732856676000385330273554875301) ^ 910952225333461776757851625100 = ((1821904450666925540337195763221 : ℕ) : ZMod 2732856676000385330273554875301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2732856676000385330273554875301 - 1) / 5 = 546571335200077066054710975060 from by norm_num]
      have h2 : (2 : ZMod 2732856676000385330273554875301) ^ 546571335200077066054710975060 = ((2613026013416107698708912060445 : ℕ) : ZMod 2732856676000385330273554875301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2732856676000385330273554875301 - 1) / 23 = 118819855478277623055371951100 from by norm_num]
      have h2 : (2 : ZMod 2732856676000385330273554875301) ^ 118819855478277623055371951100 = ((1083610958285428922354008822410 : ℕ) : ZMod 2732856676000385330273554875301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2732856676000385330273554875301 - 1) / 67 = 40788905611946049705575445900 from by norm_num]
      have h2 : (2 : ZMod 2732856676000385330273554875301) ^ 40788905611946049705575445900 = ((1961641808284462912319382547552 : ℕ) : ZMod 2732856676000385330273554875301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2732856676000385330273554875301 - 1) / 89 = 30706254786521183486219717700 from by norm_num]
      have h2 : (2 : ZMod 2732856676000385330273554875301) ^ 30706254786521183486219717700 = ((487208229010606512544489661452 : ℕ) : ZMod 2732856676000385330273554875301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2732856676000385330273554875301 - 1) / 5281 = 517488482484450924119211300 from by norm_num]
      have h2 : (2 : ZMod 2732856676000385330273554875301) ^ 517488482484450924119211300 = ((2019312497900065677559231847088 : ℕ) : ZMod 2732856676000385330273554875301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2732856676000385330273554875301 - 1) / 12207031 = 223875623482924335186300 from by norm_num]
      have h2 : (2 : ZMod 2732856676000385330273554875301) ^ 223875623482924335186300 = ((2641964771524479774179239667365 : ℕ) : ZMod 2732856676000385330273554875301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1030330938209).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2732856676000385330273554875301 - 1) / 1030330938209 = 2652406692504881700 from by norm_num]
      have h2 : (2 : ZMod 2732856676000385330273554875301) ^ 2652406692504881700 = ((2043820245381230104521874180197 : ℕ) : ZMod 2732856676000385330273554875301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 46: 13 divides 5^46 + 1 and 2732856676000385330273554875301 + 1 (5^46+1 -> 5465713352000770660547109750601 -> 2732856676000385330273554875301).
theorem ke46 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 46 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g5465713352000770660547109750601 : 5465713352000770660547109750601 ∈ P := S7 5465713352000770660547109750601 prime_5465713352000770660547109750601 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5465713352000770660547109750601 ∣ 1 + 5 ^ 46).trans hd)
  have g2732856676000385330273554875301 : 2732856676000385330273554875301 ∈ P := S1 2732856676000385330273554875301 prime_2732856676000385330273554875301 (by norm_num) (hnz (by norm_num)) 5465713352000770660547109750601 g5465713352000770660547109750601 (by norm_num)
  exact S8 13 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 13 ∣ 1 + 5 ^ 46).trans hd) 2732856676000385330273554875301 g2732856676000385330273554875301 (by norm_num)

-- e an odd multiple of 52: 3^2 divides 17 + 1 (5^52+1 -> 51169 -> 17).
theorem ke52 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 52 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g51169 : 51169 ∈ P := S7 51169 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 51169 ∣ 1 + 5 ^ 52).trans hd)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 51169 g51169 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 17 g17 (by norm_num)

theorem prime_1334402673828313149547634216455312875601 : Nat.Prime 1334402673828313149547634216455312875601 := by
  refine lucas_primality 1334402673828313149547634216455312875601 (17 : ZMod 1334402673828313149547634216455312875601) ?_ (fun q hq hd => ?_)
  · rw [show 1334402673828313149547634216455312875601 - 1 = 1334402673828313149547634216455312875600 from by norm_num]
    reduce_mod_char
  · have e : 1334402673828313149547634216455312875601 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 2, 29 ^ 1, 313 ^ 1, 449 ^ 1, 19531 ^ 1, 234750601 ^ 1, 59509429687890001 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1334402673828313149547634216455312875601 - 1) / 2 = 667201336914156574773817108227656437800 from by norm_num]
      have h2 : (17 : ZMod 1334402673828313149547634216455312875601) ^ 667201336914156574773817108227656437800 = ((1334402673828313149547634216455312875600 : ℕ) : ZMod 1334402673828313149547634216455312875601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1334402673828313149547634216455312875601 - 1) / 3 = 444800891276104383182544738818437625200 from by norm_num]
      have h2 : (17 : ZMod 1334402673828313149547634216455312875601) ^ 444800891276104383182544738818437625200 = ((562015659856042506148971184482503913347 : ℕ) : ZMod 1334402673828313149547634216455312875601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1334402673828313149547634216455312875601 - 1) / 5 = 266880534765662629909526843291062575120 from by norm_num]
      have h2 : (17 : ZMod 1334402673828313149547634216455312875601) ^ 266880534765662629909526843291062575120 = ((56292406765153430080897119725954027033 : ℕ) : ZMod 1334402673828313149547634216455312875601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1334402673828313149547634216455312875601 - 1) / 29 = 46013885304424591363711524705355616400 from by norm_num]
      have h2 : (17 : ZMod 1334402673828313149547634216455312875601) ^ 46013885304424591363711524705355616400 = ((2220446049250313080847263336181640625 : ℕ) : ZMod 1334402673828313149547634216455312875601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1334402673828313149547634216455312875601 - 1) / 313 = 4263267328524962139129821777812501200 from by norm_num]
      have h2 : (17 : ZMod 1334402673828313149547634216455312875601) ^ 4263267328524962139129821777812501200 = ((179875270005980560421893774778442339518 : ℕ) : ZMod 1334402673828313149547634216455312875601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1334402673828313149547634216455312875601 - 1) / 449 = 2971943594272412359794285560034104400 from by norm_num]
      have h2 : (17 : ZMod 1334402673828313149547634216455312875601) ^ 2971943594272412359794285560034104400 = ((603317759957235197455816973376720933123 : ℕ) : ZMod 1334402673828313149547634216455312875601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1334402673828313149547634216455312875601 - 1) / 19531 = 68322291425339877607272244967247600 from by norm_num]
      have h2 : (17 : ZMod 1334402673828313149547634216455312875601) ^ 68322291425339877607272244967247600 = ((550977158017825287040421691031702533831 : ℕ) : ZMod 1334402673828313149547634216455312875601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_234750601).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1334402673828313149547634216455312875601 - 1) / 234750601 = 5684341885149478912506103515600 from by norm_num]
      have h2 : (17 : ZMod 1334402673828313149547634216455312875601) ^ 5684341885149478912506103515600 = ((312624183572410006791583797134586825860 : ℕ) : ZMod 1334402673828313149547634216455312875601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_59509429687890001).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1334402673828313149547634216455312875601 - 1) / 59509429687890001 = 22423381988818828875600 from by norm_num]
      have h2 : (17 : ZMod 1334402673828313149547634216455312875601) ^ 22423381988818828875600 = ((529336373435275237381775308528691483920 : ℕ) : ZMod 1334402673828313149547634216455312875601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 58: 7 divides 13 + 1 and 41 + 1 (5^58+1 -> 13; 5^58+1 -> 1334402673828313149547634216455312875601 -> 163 -> 41).
theorem ke58 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 58 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13 ∣ 1 + 5 ^ 58).trans hd)
  have g1334402673828313149547634216455312875601 : 1334402673828313149547634216455312875601 ∈ P := S7 1334402673828313149547634216455312875601 prime_1334402673828313149547634216455312875601 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1334402673828313149547634216455312875601 ∣ 1 + 5 ^ 58).trans hd)
  have g163 : 163 ∈ P := S1 163 (by norm_num) (by norm_num) (hnz (by norm_num)) 1334402673828313149547634216455312875601 g1334402673828313149547634216455312875601 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 163 g163 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 41 g41 (by norm_num) (by norm_num)) (by norm_num)

-- e an odd multiple of 61: 3 divides 5^61 + 1 and 9029 + 1 (5^61+1 -> 9029).
theorem ke61 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 61 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g9029 : 9029 ∈ P := S7 9029 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 9029 ∣ 1 + 5 ^ 61).trans hd)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 61).trans hd) 9029 g9029 (by norm_num)

theorem prime_437195617 : Nat.Prime 437195617 := by
  refine lucas_primality 437195617 (7 : ZMod 437195617) ?_ (fun q hq hd => ?_)
  · rw [show 437195617 - 1 = 437195616 from by norm_num]
    reduce_mod_char
  · have e : 437195617 - 1 = [2 ^ 5, 3 ^ 1, 11 ^ 1, 13 ^ 1, 31847 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (437195617 - 1) / 2 = 218597808 from by norm_num]
      have h2 : (7 : ZMod 437195617) ^ 218597808 = ((437195616 : ℕ) : ZMod 437195617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (437195617 - 1) / 3 = 145731872 from by norm_num]
      have h2 : (7 : ZMod 437195617) ^ 145731872 = ((128507264 : ℕ) : ZMod 437195617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (437195617 - 1) / 11 = 39745056 from by norm_num]
      have h2 : (7 : ZMod 437195617) ^ 39745056 = ((130950739 : ℕ) : ZMod 437195617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (437195617 - 1) / 13 = 33630432 from by norm_num]
      have h2 : (7 : ZMod 437195617) ^ 33630432 = ((369247023 : ℕ) : ZMod 437195617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (437195617 - 1) / 31847 = 13728 from by norm_num]
      have h2 : (7 : ZMod 437195617) ^ 13728 = ((408127421 : ℕ) : ZMod 437195617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8124604717965111529 : Nat.Prime 8124604717965111529 := by
  refine lucas_primality 8124604717965111529 (7 : ZMod 8124604717965111529) ?_ (fun q hq hd => ?_)
  · rw [show 8124604717965111529 - 1 = 8124604717965111528 from by norm_num]
    reduce_mod_char
  · have e : 8124604717965111529 - 1 = [2 ^ 3, 3 ^ 1, 19 ^ 1, 31 ^ 1, 89 ^ 1, 14771 ^ 1, 437195617 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8124604717965111529 - 1) / 2 = 4062302358982555764 from by norm_num]
      have h2 : (7 : ZMod 8124604717965111529) ^ 4062302358982555764 = ((8124604717965111528 : ℕ) : ZMod 8124604717965111529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8124604717965111529 - 1) / 3 = 2708201572655037176 from by norm_num]
      have h2 : (7 : ZMod 8124604717965111529) ^ 2708201572655037176 = ((6226094177290934408 : ℕ) : ZMod 8124604717965111529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8124604717965111529 - 1) / 19 = 427610774629742712 from by norm_num]
      have h2 : (7 : ZMod 8124604717965111529) ^ 427610774629742712 = ((7734100806726658010 : ℕ) : ZMod 8124604717965111529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8124604717965111529 - 1) / 31 = 262084023160164888 from by norm_num]
      have h2 : (7 : ZMod 8124604717965111529) ^ 262084023160164888 = ((95367431640625 : ℕ) : ZMod 8124604717965111529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8124604717965111529 - 1) / 89 = 91287693460282152 from by norm_num]
      have h2 : (7 : ZMod 8124604717965111529) ^ 91287693460282152 = ((2599486538690556363 : ℕ) : ZMod 8124604717965111529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8124604717965111529 - 1) / 14771 = 550037554530168 from by norm_num]
      have h2 : (7 : ZMod 8124604717965111529) ^ 550037554530168 = ((7850996936420835683 : ℕ) : ZMod 8124604717965111529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_437195617).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8124604717965111529 - 1) / 437195617 = 18583454184 from by norm_num]
      have h2 : (7 : ZMod 8124604717965111529) ^ 18583454184 = ((1189526019350091649 : ℕ) : ZMod 8124604717965111529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 62: 7 divides 13 + 1 and 8124604717965111529 + 1 (5^62+1 -> 13; 5^62+1 -> 8124604717965111529).
theorem ke62 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 62 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13 ∣ 1 + 5 ^ 62).trans hd)
  have g8124604717965111529 : 8124604717965111529 ∈ P := S7 8124604717965111529 prime_8124604717965111529 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8124604717965111529 ∣ 1 + 5 ^ 62).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 8124604717965111529 g8124604717965111529 (by norm_num) (by norm_num)) (by norm_num)

theorem prime_502535581 : Nat.Prime 502535581 := by
  refine lucas_primality 502535581 (2 : ZMod 502535581) ?_ (fun q hq hd => ?_)
  · rw [show 502535581 - 1 = 502535580 from by norm_num]
    reduce_mod_char
  · have e : 502535581 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 8375593 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (502535581 - 1) / 2 = 251267790 from by norm_num]
      have h2 : (2 : ZMod 502535581) ^ 251267790 = ((502535580 : ℕ) : ZMod 502535581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (502535581 - 1) / 3 = 167511860 from by norm_num]
      have h2 : (2 : ZMod 502535581) ^ 167511860 = ((459736365 : ℕ) : ZMod 502535581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (502535581 - 1) / 5 = 100507116 from by norm_num]
      have h2 : (2 : ZMod 502535581) ^ 100507116 = ((72812358 : ℕ) : ZMod 502535581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (502535581 - 1) / 8375593 = 60 from by norm_num]
      have h2 : (2 : ZMod 502535581) ^ 60 = ((104414371 : ℕ) : ZMod 502535581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3666499598977 : Nat.Prime 3666499598977 := by
  refine lucas_primality 3666499598977 (7 : ZMod 3666499598977) ?_ (fun q hq hd => ?_)
  · rw [show 3666499598977 - 1 = 3666499598976 from by norm_num]
    reduce_mod_char
  · have e : 3666499598977 - 1 = [2 ^ 7, 3 ^ 1, 19 ^ 1, 502535581 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3666499598977 - 1) / 2 = 1833249799488 from by norm_num]
      have h2 : (7 : ZMod 3666499598977) ^ 1833249799488 = ((3666499598976 : ℕ) : ZMod 3666499598977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3666499598977 - 1) / 3 = 1222166532992 from by norm_num]
      have h2 : (7 : ZMod 3666499598977) ^ 1222166532992 = ((1187453411854 : ℕ) : ZMod 3666499598977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3666499598977 - 1) / 19 = 192973663104 from by norm_num]
      have h2 : (7 : ZMod 3666499598977) ^ 192973663104 = ((3110808012070 : ℕ) : ZMod 3666499598977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_502535581).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3666499598977 - 1) / 502535581 = 7296 from by norm_num]
      have h2 : (7 : ZMod 3666499598977) ^ 7296 = ((345948855315 : ℕ) : ZMod 3666499598977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 64: 3 divides 11 + 1 and 113 + 1 (5^64+1 -> 769 -> 11; 5^64+1 -> 3666499598977 -> 113).
theorem ke64 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 64 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g769 : 769 ∈ P := S7 769 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 769 ∣ 1 + 5 ^ 64).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 769 g769 (by norm_num)
  have g3666499598977 : 3666499598977 ∈ P := S7 3666499598977 prime_3666499598977 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3666499598977 ∣ 1 + 5 ^ 64).trans hd)
  have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 3666499598977 g3666499598977 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 11 g11 113 g113 (by norm_num) (by norm_num)) (by norm_num)

theorem prime_5855734783 : Nat.Prime 5855734783 := by
  refine lucas_primality 5855734783 (3 : ZMod 5855734783) ?_ (fun q hq hd => ?_)
  · rw [show 5855734783 - 1 = 5855734782 from by norm_num]
    reduce_mod_char
  · have e : 5855734783 - 1 = [2 ^ 1, 3 ^ 6, 103 ^ 1, 38993 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5855734783 - 1) / 2 = 2927867391 from by norm_num]
      have h2 : (3 : ZMod 5855734783) ^ 2927867391 = ((5855734782 : ℕ) : ZMod 5855734783) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5855734783 - 1) / 3 = 1951911594 from by norm_num]
      have h2 : (3 : ZMod 5855734783) ^ 1951911594 = ((2936648275 : ℕ) : ZMod 5855734783) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5855734783 - 1) / 103 = 56851794 from by norm_num]
      have h2 : (3 : ZMod 5855734783) ^ 56851794 = ((795928112 : ℕ) : ZMod 5855734783) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5855734783 - 1) / 38993 = 150174 from by norm_num]
      have h2 : (3 : ZMod 5855734783) ^ 150174 = ((5609911600 : ℕ) : ZMod 5855734783) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_386478495679 : Nat.Prime 386478495679 := by
  refine lucas_primality 386478495679 (3 : ZMod 386478495679) ?_ (fun q hq hd => ?_)
  · rw [show 386478495679 - 1 = 386478495678 from by norm_num]
    reduce_mod_char
  · have e : 386478495679 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 5855734783 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (386478495679 - 1) / 2 = 193239247839 from by norm_num]
      have h2 : (3 : ZMod 386478495679) ^ 193239247839 = ((386478495678 : ℕ) : ZMod 386478495679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (386478495679 - 1) / 3 = 128826165226 from by norm_num]
      have h2 : (3 : ZMod 386478495679) ^ 128826165226 = ((48828125 : ℕ) : ZMod 386478495679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (386478495679 - 1) / 11 = 35134408698 from by norm_num]
      have h2 : (3 : ZMod 386478495679) ^ 35134408698 = ((250438065200 : ℕ) : ZMod 386478495679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_5855734783).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (386478495679 - 1) / 5855734783 = 66 from by norm_num]
      have h2 : (3 : ZMod 386478495679) ^ 66 = ((122676781830 : ℕ) : ZMod 386478495679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_190771747 : Nat.Prime 190771747 := by
  refine lucas_primality 190771747 (2 : ZMod 190771747) ?_ (fun q hq hd => ?_)
  · rw [show 190771747 - 1 = 190771746 from by norm_num]
    reduce_mod_char
  · have e : 190771747 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 2, 71 ^ 1, 3701 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (190771747 - 1) / 2 = 95385873 from by norm_num]
      have h2 : (2 : ZMod 190771747) ^ 95385873 = ((190771746 : ℕ) : ZMod 190771747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (190771747 - 1) / 3 = 63590582 from by norm_num]
      have h2 : (2 : ZMod 190771747) ^ 63590582 = ((141943622 : ℕ) : ZMod 190771747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (190771747 - 1) / 11 = 17342886 from by norm_num]
      have h2 : (2 : ZMod 190771747) ^ 17342886 = ((188818622 : ℕ) : ZMod 190771747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (190771747 - 1) / 71 = 2686926 from by norm_num]
      have h2 : (2 : ZMod 190771747) ^ 2686926 = ((79765162 : ℕ) : ZMod 190771747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (190771747 - 1) / 3701 = 51546 from by norm_num]
      have h2 : (2 : ZMod 190771747) ^ 51546 = ((56046893 : ℕ) : ZMod 190771747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11293772630057337854244300009061892827351888021 : Nat.Prime 11293772630057337854244300009061892827351888021 := by
  refine lucas_primality 11293772630057337854244300009061892827351888021 (2 : ZMod 11293772630057337854244300009061892827351888021) ?_ (fun q hq hd => ?_)
  · rw [show 11293772630057337854244300009061892827351888021 - 1 = 11293772630057337854244300009061892827351888020 from by norm_num]
    reduce_mod_char
  · have e : 11293772630057337854244300009061892827351888021 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 7 ^ 1, 23 ^ 1, 31 ^ 1, 67 ^ 1, 199 ^ 1, 5281 ^ 1, 595123 ^ 1, 12207031 ^ 1, 190771747 ^ 1, 386478495679 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11293772630057337854244300009061892827351888021 - 1) / 2 = 5646886315028668927122150004530946413675944010 from by norm_num]
      have h2 : (2 : ZMod 11293772630057337854244300009061892827351888021) ^ 5646886315028668927122150004530946413675944010 = ((11293772630057337854244300009061892827351888020 : ℕ) : ZMod 11293772630057337854244300009061892827351888021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11293772630057337854244300009061892827351888021 - 1) / 3 = 3764590876685779284748100003020630942450629340 from by norm_num]
      have h2 : (2 : ZMod 11293772630057337854244300009061892827351888021) ^ 3764590876685779284748100003020630942450629340 = ((1121615310015528681491158641251578764252020675 : ℕ) : ZMod 11293772630057337854244300009061892827351888021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11293772630057337854244300009061892827351888021 - 1) / 5 = 2258754526011467570848860001812378565470377604 from by norm_num]
      have h2 : (2 : ZMod 11293772630057337854244300009061892827351888021) ^ 2258754526011467570848860001812378565470377604 = ((5467331834395471753558249867538407709271410417 : ℕ) : ZMod 11293772630057337854244300009061892827351888021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11293772630057337854244300009061892827351888021 - 1) / 7 = 1613396090008191122034900001294556118193126860 from by norm_num]
      have h2 : (2 : ZMod 11293772630057337854244300009061892827351888021) ^ 1613396090008191122034900001294556118193126860 = ((2585194456985871801736290403233224371762371935 : ℕ) : ZMod 11293772630057337854244300009061892827351888021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11293772630057337854244300009061892827351888021 - 1) / 23 = 491033592611188602358447826480951862058777740 from by norm_num]
      have h2 : (2 : ZMod 11293772630057337854244300009061892827351888021) ^ 491033592611188602358447826480951862058777740 = ((1241785582829307718491801296047842796466439932 : ℕ) : ZMod 11293772630057337854244300009061892827351888021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11293772630057337854244300009061892827351888021 - 1) / 31 = 364315246130881866265945161582641704108125420 from by norm_num]
      have h2 : (2 : ZMod 11293772630057337854244300009061892827351888021) ^ 364315246130881866265945161582641704108125420 = ((4571610496004734681063378865586816850900795332 : ℕ) : ZMod 11293772630057337854244300009061892827351888021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11293772630057337854244300009061892827351888021 - 1) / 67 = 168563770597870714242452238941222281005252060 from by norm_num]
      have h2 : (2 : ZMod 11293772630057337854244300009061892827351888021) ^ 168563770597870714242452238941222281005252060 = ((3552713678800500929355621337890625 : ℕ) : ZMod 11293772630057337854244300009061892827351888021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11293772630057337854244300009061892827351888021 - 1) / 199 = 56752626281695165096705025171165290589707980 from by norm_num]
      have h2 : (2 : ZMod 11293772630057337854244300009061892827351888021) ^ 56752626281695165096705025171165290589707980 = ((4125830703467287866901659114835300286821506617 : ℕ) : ZMod 11293772630057337854244300009061892827351888021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11293772630057337854244300009061892827351888021 - 1) / 5281 = 2138567057386354450718481349945444580070420 from by norm_num]
      have h2 : (2 : ZMod 11293772630057337854244300009061892827351888021) ^ 2138567057386354450718481349945444580070420 = ((1172455934995218909471755172017310622270237843 : ℕ) : ZMod 11293772630057337854244300009061892827351888021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11293772630057337854244300009061892827351888021 - 1) / 595123 = 18977207451329116593114868706237017939740 from by norm_num]
      have h2 : (2 : ZMod 11293772630057337854244300009061892827351888021) ^ 18977207451329116593114868706237017939740 = ((11226181588476231166425109829868567897205611129 : ℕ) : ZMod 11293772630057337854244300009061892827351888021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11293772630057337854244300009061892827351888021 - 1) / 12207031 = 925185872802103792006778717041178385420 from by norm_num]
      have h2 : (2 : ZMod 11293772630057337854244300009061892827351888021) ^ 925185872802103792006778717041178385420 = ((5143281027206577961830631200421281916587426092 : ℕ) : ZMod 11293772630057337854244300009061892827351888021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_190771747).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11293772630057337854244300009061892827351888021 - 1) / 190771747 = 59200446647151256911456076402455405660 from by norm_num]
      have h2 : (2 : ZMod 11293772630057337854244300009061892827351888021) ^ 59200446647151256911456076402455405660 = ((1613894449426835745604710010033318701569368205 : ℕ) : ZMod 11293772630057337854244300009061892827351888021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_386478495679).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11293772630057337854244300009061892827351888021 - 1) / 386478495679 = 29222253647555286685625963094070380 from by norm_num]
      have h2 : (2 : ZMod 11293772630057337854244300009061892827351888021) ^ 29222253647555286685625963094070380 = ((2998008727486167934038993937335001079296855847 : ℕ) : ZMod 11293772630057337854244300009061892827351888021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 67: 3^2 divides 17 + 1 (5^67+1 -> 11293772630057337854244300009061892827351888021 -> 7717 -> 17).
theorem ke67 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 67 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g11293772630057337854244300009061892827351888021 : 11293772630057337854244300009061892827351888021 ∈ P := S7 11293772630057337854244300009061892827351888021 prime_11293772630057337854244300009061892827351888021 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 11293772630057337854244300009061892827351888021 ∣ 1 + 5 ^ 67).trans hd)
  have g7717 : 7717 ∈ P := S1 7717 (by norm_num) (by norm_num) (hnz (by norm_num)) 11293772630057337854244300009061892827351888021 g11293772630057337854244300009061892827351888021 (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 7717 g7717 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 17 g17 (by norm_num)

-- e an odd multiple of 68: 3 divides 137 + 1 and 23 + 1 (5^68+1 -> 137; 5^68+1 -> 137 -> 23).
theorem ke68 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 68 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g137 : 137 ∈ P := S7 137 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 137 ∣ 1 + 5 ^ 68).trans hd)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 23 g23 (by norm_num) (by norm_num)) (by norm_num)

theorem prime_63554310563 : Nat.Prime 63554310563 := by
  refine lucas_primality 63554310563 (2 : ZMod 63554310563) ?_ (fun q hq hd => ?_)
  · rw [show 63554310563 - 1 = 63554310562 from by norm_num]
    reduce_mod_char
  · have e : 63554310563 - 1 = [2 ^ 1, 23 ^ 1, 73 ^ 1, 18926239 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63554310563 - 1) / 2 = 31777155281 from by norm_num]
      have h2 : (2 : ZMod 63554310563) ^ 31777155281 = ((63554310562 : ℕ) : ZMod 63554310563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63554310563 - 1) / 23 = 2763230894 from by norm_num]
      have h2 : (2 : ZMod 63554310563) ^ 2763230894 = ((58241415415 : ℕ) : ZMod 63554310563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63554310563 - 1) / 73 = 870606994 from by norm_num]
      have h2 : (2 : ZMod 63554310563) ^ 870606994 = ((38508749110 : ℕ) : ZMod 63554310563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63554310563 - 1) / 18926239 = 3358 from by norm_num]
      have h2 : (2 : ZMod 63554310563) ^ 3358 = ((62548560917 : ℕ) : ZMod 63554310563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 73: 3 divides 5^73 + 1 and 63554310563 + 1 (5^73+1 -> 63554310563).
theorem ke73 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 73 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g63554310563 : 63554310563 ∈ P := S7 63554310563 prime_63554310563 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 63554310563 ∣ 1 + 5 ^ 73).trans hd)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 73).trans hd) 63554310563 g63554310563 (by norm_num)

-- e an odd multiple of 74: 3 divides 977 + 1 and 41 + 1 (5^74+1 -> 9769 -> 977; 5^74+1 -> 9769 -> 977 -> 163 -> 41).
theorem ke74 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 74 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g9769 : 9769 ∈ P := S7 9769 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 9769 ∣ 1 + 5 ^ 74).trans hd)
  have g977 : 977 ∈ P := S1 977 (by norm_num) (by norm_num) (hnz (by norm_num)) 9769 g9769 (by norm_num)
  have g163 : 163 ∈ P := S1 163 (by norm_num) (by norm_num) (hnz (by norm_num)) 977 g977 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 163 g163 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 977 g977 41 g41 (by norm_num) (by norm_num)) (by norm_num)

theorem prime_165909277 : Nat.Prime 165909277 := by
  refine lucas_primality 165909277 (2 : ZMod 165909277) ?_ (fun q hq hd => ?_)
  · rw [show 165909277 - 1 = 165909276 from by norm_num]
    reduce_mod_char
  · have e : 165909277 - 1 = [2 ^ 2, 3 ^ 3, 13 ^ 1, 118169 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165909277 - 1) / 2 = 82954638 from by norm_num]
      have h2 : (2 : ZMod 165909277) ^ 82954638 = ((165909276 : ℕ) : ZMod 165909277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165909277 - 1) / 3 = 55303092 from by norm_num]
      have h2 : (2 : ZMod 165909277) ^ 55303092 = ((100630300 : ℕ) : ZMod 165909277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165909277 - 1) / 13 = 12762252 from by norm_num]
      have h2 : (2 : ZMod 165909277) ^ 12762252 = ((98736556 : ℕ) : ZMod 165909277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165909277 - 1) / 118169 = 1404 from by norm_num]
      have h2 : (2 : ZMod 165909277) ^ 1404 = ((51819922 : ℕ) : ZMod 165909277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_21363981507860375753 : Nat.Prime 21363981507860375753 := by
  refine lucas_primality 21363981507860375753 (6 : ZMod 21363981507860375753) ?_ (fun q hq hd => ?_)
  · rw [show 21363981507860375753 - 1 = 21363981507860375752 from by norm_num]
    reduce_mod_char
  · have e : 21363981507860375753 - 1 = [2 ^ 3, 19 ^ 1, 20743 ^ 1, 40841 ^ 1, 165909277 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21363981507860375753 - 1) / 2 = 10681990753930187876 from by norm_num]
      have h2 : (6 : ZMod 21363981507860375753) ^ 10681990753930187876 = ((21363981507860375752 : ℕ) : ZMod 21363981507860375753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21363981507860375753 - 1) / 19 = 1124420079361072408 from by norm_num]
      have h2 : (6 : ZMod 21363981507860375753) ^ 1124420079361072408 = ((6070590600779593142 : ℕ) : ZMod 21363981507860375753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21363981507860375753 - 1) / 20743 = 1029936918857464 from by norm_num]
      have h2 : (6 : ZMod 21363981507860375753) ^ 1029936918857464 = ((3430441500169963182 : ℕ) : ZMod 21363981507860375753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21363981507860375753 - 1) / 40841 = 523101332187272 from by norm_num]
      have h2 : (6 : ZMod 21363981507860375753) ^ 523101332187272 = ((2220924226271666650 : ℕ) : ZMod 21363981507860375753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_165909277).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21363981507860375753 - 1) / 165909277 = 128769059176 from by norm_num]
      have h2 : (6 : ZMod 21363981507860375753) ^ 128769059176 = ((8834336673133135465 : ℕ) : ZMod 21363981507860375753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 76: 3^2 divides 21363981507860375753 + 1 (5^76+1 -> 21363981507860375753).
theorem ke76 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 76 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g21363981507860375753 : 21363981507860375753 ∈ P := S7 21363981507860375753 prime_21363981507860375753 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 21363981507860375753 ∣ 1 + 5 ^ 76).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 21363981507860375753 g21363981507860375753 (by norm_num)

-- e an odd multiple of 79: 3 divides 5^79 + 1 and 18251687 + 1 (5^79+1 -> 18251687).
theorem ke79 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 79 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g18251687 : 18251687 ∈ P := S7 18251687 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 18251687 ∣ 1 + 5 ^ 79).trans hd)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 79).trans hd) 18251687 g18251687 (by norm_num)

-- e an odd multiple of 82: 11^2 divides 193357 + 1 (5^82+1 -> 193357).
theorem ke82 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 82 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g193357 : 193357 ∈ P := S7 193357 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 193357 ∣ 1 + 5 ^ 82).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 193357 g193357 (by norm_num)

-- e an odd multiple of 86: 3 divides 173 + 1 and 29 + 1 (5^86+1 -> 173; 5^86+1 -> 173 -> 29).
theorem ke86 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 86 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g173 : 173 ∈ P := S7 173 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 173 ∣ 1 + 5 ^ 86).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 173 g173 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 173 g173 29 g29 (by norm_num) (by norm_num)) (by norm_num)

theorem prime_3104238623 : Nat.Prime 3104238623 := by
  refine lucas_primality 3104238623 (5 : ZMod 3104238623) ?_ (fun q hq hd => ?_)
  · rw [show 3104238623 - 1 = 3104238622 from by norm_num]
    reduce_mod_char
  · have e : 3104238623 - 1 = [2 ^ 1, 677 ^ 1, 2292643 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3104238623 - 1) / 2 = 1552119311 from by norm_num]
      have h2 : (5 : ZMod 3104238623) ^ 1552119311 = ((3104238622 : ℕ) : ZMod 3104238623) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3104238623 - 1) / 677 = 4585286 from by norm_num]
      have h2 : (5 : ZMod 3104238623) ^ 4585286 = ((2501122737 : ℕ) : ZMod 3104238623) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3104238623 - 1) / 2292643 = 1354 from by norm_num]
      have h2 : (5 : ZMod 3104238623) ^ 1354 = ((552623086 : ℕ) : ZMod 3104238623) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_150220315444217 : Nat.Prime 150220315444217 := by
  refine lucas_primality 150220315444217 (3 : ZMod 150220315444217) ?_ (fun q hq hd => ?_)
  · rw [show 150220315444217 - 1 = 150220315444216 from by norm_num]
    reduce_mod_char
  · have e : 150220315444217 - 1 = [2 ^ 3, 23 ^ 1, 263 ^ 1, 3104238623 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (150220315444217 - 1) / 2 = 75110157722108 from by norm_num]
      have h2 : (3 : ZMod 150220315444217) ^ 75110157722108 = ((150220315444216 : ℕ) : ZMod 150220315444217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (150220315444217 - 1) / 23 = 6531318062792 from by norm_num]
      have h2 : (3 : ZMod 150220315444217) ^ 6531318062792 = ((11472789408069 : ℕ) : ZMod 150220315444217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (150220315444217 - 1) / 263 = 571179906632 from by norm_num]
      have h2 : (3 : ZMod 150220315444217) ^ 571179906632 = ((39122146990073 : ℕ) : ZMod 150220315444217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3104238623).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (150220315444217 - 1) / 3104238623 = 48392 from by norm_num]
      have h2 : (3 : ZMod 150220315444217) ^ 48392 = ((99397179422657 : ℕ) : ZMod 150220315444217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 92: 3^2 divides 41039 + 1 (5^92+1 -> 150220315444217 -> 41039).
theorem ke92 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 92 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g150220315444217 : 150220315444217 ∈ P := S7 150220315444217 prime_150220315444217 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 150220315444217 ∣ 1 + 5 ^ 92).trans hd)
  have g41039 : 41039 ∈ P := S1 41039 (by norm_num) (by norm_num) (hnz (by norm_num)) 150220315444217 g150220315444217 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 41039 g41039 (by norm_num)

-- e an odd multiple of 94: 3^2 divides 17 + 1 (5^94+1 -> 12409 -> 17).
theorem ke94 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 94 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g12409 : 12409 ∈ P := S7 12409 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 12409 ∣ 1 + 5 ^ 94).trans hd)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 12409 g12409 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 17 g17 (by norm_num)

-- e an odd multiple of 97: 3 divides 5^97 + 1 and 261707 + 1 (5^97+1 -> 261707).
theorem ke97 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 97 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g261707 : 261707 ∈ P := S7 261707 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 261707 ∣ 1 + 5 ^ 97).trans hd)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 97).trans hd) 261707 g261707 (by norm_num)

theorem prime_654652168021 : Nat.Prime 654652168021 := by
  refine lucas_primality 654652168021 (6 : ZMod 654652168021) ?_ (fun q hq hd => ?_)
  · rw [show 654652168021 - 1 = 654652168020 from by norm_num]
    reduce_mod_char
  · have e : 654652168021 - 1 = [2 ^ 2, 3 ^ 2, 5 ^ 1, 17 ^ 1, 23 ^ 1, 9301679 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (654652168021 - 1) / 2 = 327326084010 from by norm_num]
      have h2 : (6 : ZMod 654652168021) ^ 327326084010 = ((654652168020 : ℕ) : ZMod 654652168021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (654652168021 - 1) / 3 = 218217389340 from by norm_num]
      have h2 : (6 : ZMod 654652168021) ^ 218217389340 = ((546364882916 : ℕ) : ZMod 654652168021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (654652168021 - 1) / 5 = 130930433604 from by norm_num]
      have h2 : (6 : ZMod 654652168021) ^ 130930433604 = ((618011042866 : ℕ) : ZMod 654652168021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (654652168021 - 1) / 17 = 38508951060 from by norm_num]
      have h2 : (6 : ZMod 654652168021) ^ 38508951060 = ((15625 : ℕ) : ZMod 654652168021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (654652168021 - 1) / 23 = 28463137740 from by norm_num]
      have h2 : (6 : ZMod 654652168021) ^ 28463137740 = ((213374264158 : ℕ) : ZMod 654652168021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (654652168021 - 1) / 9301679 = 70380 from by norm_num]
      have h2 : (6 : ZMod 654652168021) ^ 70380 = ((310435232438 : ℕ) : ZMod 654652168021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_60119016343 : Nat.Prime 60119016343 := by
  refine lucas_primality 60119016343 (3 : ZMod 60119016343) ?_ (fun q hq hd => ?_)
  · rw [show 60119016343 - 1 = 60119016342 from by norm_num]
    reduce_mod_char
  · have e : 60119016343 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 11 ^ 1, 17 ^ 2, 193 ^ 1, 2333 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60119016343 - 1) / 2 = 30059508171 from by norm_num]
      have h2 : (3 : ZMod 60119016343) ^ 30059508171 = ((60119016342 : ℕ) : ZMod 60119016343) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60119016343 - 1) / 3 = 20039672114 from by norm_num]
      have h2 : (3 : ZMod 60119016343) ^ 20039672114 = ((41511257008 : ℕ) : ZMod 60119016343) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60119016343 - 1) / 7 = 8588430906 from by norm_num]
      have h2 : (3 : ZMod 60119016343) ^ 8588430906 = ((5354731709 : ℕ) : ZMod 60119016343) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60119016343 - 1) / 11 = 5465365122 from by norm_num]
      have h2 : (3 : ZMod 60119016343) ^ 5465365122 = ((10609697037 : ℕ) : ZMod 60119016343) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60119016343 - 1) / 17 = 3536412726 from by norm_num]
      have h2 : (3 : ZMod 60119016343) ^ 3536412726 = ((58360655353 : ℕ) : ZMod 60119016343) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60119016343 - 1) / 193 = 311497494 from by norm_num]
      have h2 : (3 : ZMod 60119016343) ^ 311497494 = ((53098588946 : ℕ) : ZMod 60119016343) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60119016343 - 1) / 2333 = 25768974 from by norm_num]
      have h2 : (3 : ZMod 60119016343) ^ 25768974 = ((12201379632 : ℕ) : ZMod 60119016343) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_466344409 : Nat.Prime 466344409 := by
  refine lucas_primality 466344409 (7 : ZMod 466344409) ?_ (fun q hq hd => ?_)
  · rw [show 466344409 - 1 = 466344408 from by norm_num]
    reduce_mod_char
  · have e : 466344409 - 1 = [2 ^ 3, 3 ^ 1, 17 ^ 1, 31 ^ 1, 36871 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (466344409 - 1) / 2 = 233172204 from by norm_num]
      have h2 : (7 : ZMod 466344409) ^ 233172204 = ((466344408 : ℕ) : ZMod 466344409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (466344409 - 1) / 3 = 155448136 from by norm_num]
      have h2 : (7 : ZMod 466344409) ^ 155448136 = ((389773979 : ℕ) : ZMod 466344409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (466344409 - 1) / 17 = 27432024 from by norm_num]
      have h2 : (7 : ZMod 466344409) ^ 27432024 = ((5 : ℕ) : ZMod 466344409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (466344409 - 1) / 31 = 15043368 from by norm_num]
      have h2 : (7 : ZMod 466344409) ^ 15043368 = ((393150086 : ℕ) : ZMod 466344409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (466344409 - 1) / 36871 = 12648 from by norm_num]
      have h2 : (7 : ZMod 466344409) ^ 12648 = ((263193984 : ℕ) : ZMod 466344409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_164346021921044126127443451100580464515251340647713125993808110555013021 : Nat.Prime 164346021921044126127443451100580464515251340647713125993808110555013021 := by
  refine lucas_primality 164346021921044126127443451100580464515251340647713125993808110555013021 (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ?_ (fun q hq hd => ?_)
  · rw [show 164346021921044126127443451100580464515251340647713125993808110555013021 - 1 = 164346021921044126127443451100580464515251340647713125993808110555013020 from by norm_num]
    reduce_mod_char
  · have e : 164346021921044126127443451100580464515251340647713125993808110555013021 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 7 ^ 1, 31 ^ 1, 103 ^ 1, 409 ^ 1, 3061 ^ 1, 8467 ^ 1, 90271 ^ 1, 317731 ^ 1, 528667 ^ 1, 41540861 ^ 1, 466344409 ^ 1, 60119016343 ^ 1, 654652168021 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 2 = 82173010960522063063721725550290232257625670323856562996904055277506510 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 82173010960522063063721725550290232257625670323856562996904055277506510 = ((164346021921044126127443451100580464515251340647713125993808110555013020 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 3 = 54782007307014708709147817033526821505083780215904375331269370185004340 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 54782007307014708709147817033526821505083780215904375331269370185004340 = ((85017410894196298847883441476318243396366875624603560019465102249179421 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 5 = 32869204384208825225488690220116092903050268129542625198761622111002604 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 32869204384208825225488690220116092903050268129542625198761622111002604 = ((62975793243504884484223774245065142294628037246066983389788294988212839 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 7 = 23478003131577732303920493014368637787893048663959017999115444365001860 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 23478003131577732303920493014368637787893048663959017999115444365001860 = ((45036477366593994096159596996189198885864042661553598280716377261855670 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 31 = 5301484578098197617014304874212273048879075504764939548187358405000420 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 5301484578098197617014304874212273048879075504764939548187358405000420 = ((7647059766272543388081230864788569248053760051352731649242157657720006 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 103 = 1595592445835379865314984962141557907915061559686535203823379714126340 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 1595592445835379865314984962141557907915061559686535203823379714126340 = ((55511151231257827021181583404541015625 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 409 = 401824014476880503979079342544206514707215991803699574556988045366780 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 401824014476880503979079342544206514707215991803699574556988045366780 = ((22286265674065711811151993734764607587559054705722925513474689760983698 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 3061 = 53690304449867404811317690656837786512659699656227744525909216123820 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 53690304449867404811317690656837786512659699656227744525909216123820 = ((4826494801470240467825218555527111723131034935836999506207334670461741 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 8467 = 19410183290544954071978676166361221745039723709426376047455782515060 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 19410183290544954071978676166361221745039723709426376047455782515060 = ((16844173123677196874818350838070508586131659192160219208126738845179279 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 90271 = 1820584926732218831379329475696297421267642328629494810003302395620 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 1820584926732218831379329475696297421267642328629494810003302395620 = ((3833179710646086923551694817246532600030904622842111182795929005135738 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 317731 = 517248936745373054966130000222139056356639234596917285357135786420 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 517248936745373054966130000222139056356639234596917285357135786420 = ((157304563665186395814208623525841113751401720635885824182096244963074106 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 528667 = 310868697915784654853515447532341652713809147625467687587475879060 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 310868697915784654853515447532341652713809147625467687587475879060 = ((158880262474155406112618098737727765260319178213874081515952309324136929 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 41540861 = 3956249773471092140517825355150449686520732939254993438720687820 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 3956249773471092140517825355150449686520732939254993438720687820 = ((10288113242819729647860203326421698887945108385809868597771800611804427 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_466344409).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 466344409 = 352413406806908080948909695410501778987236320973482767740886780 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 352413406806908080948909695410501778987236320973482767740886780 = ((151834049932325704494894680016894184455235155482366315558803784096831375 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_60119016343).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 60119016343 = 2733677826386789691913363764541600169861104885438480069075140 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 2733677826386789691913363764541600169861104885438480069075140 = ((146518724196696326003808384614593808978407250768178314386035313481547322 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_654652168021).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (164346021921044126127443451100580464515251340647713125993808110555013021 - 1) / 654652168021 = 251043271448804271625078558353531359251264531218105690040620 from by norm_num]
      have h2 : (2 : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) ^ 251043271448804271625078558353531359251264531218105690040620 = ((150184010691685011569864721527869696932352308358027694229654888349311749 : ℕ) : ZMod 164346021921044126127443451100580464515251340647713125993808110555013021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 103: 3^2 divides 17 + 1 (5^103+1 -> 164346021921044126127443451100580464515251340647713125993808110555013021 -> 17).
theorem ke103 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 103 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g164346021921044126127443451100580464515251340647713125993808110555013021 : 164346021921044126127443451100580464515251340647713125993808110555013021 ∈ P := S7 164346021921044126127443451100580464515251340647713125993808110555013021 prime_164346021921044126127443451100580464515251340647713125993808110555013021 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 164346021921044126127443451100580464515251340647713125993808110555013021 ∣ 1 + 5 ^ 103).trans hd)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 164346021921044126127443451100580464515251340647713125993808110555013021 g164346021921044126127443451100580464515251340647713125993808110555013021 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 17 g17 (by norm_num)

theorem prime_49026644363 : Nat.Prime 49026644363 := by
  refine lucas_primality 49026644363 (2 : ZMod 49026644363) ?_ (fun q hq hd => ?_)
  · rw [show 49026644363 - 1 = 49026644362 from by norm_num]
    reduce_mod_char
  · have e : 49026644363 - 1 = [2 ^ 1, 2731 ^ 1, 8975951 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49026644363 - 1) / 2 = 24513322181 from by norm_num]
      have h2 : (2 : ZMod 49026644363) ^ 24513322181 = ((49026644362 : ℕ) : ZMod 49026644363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49026644363 - 1) / 2731 = 17951902 from by norm_num]
      have h2 : (2 : ZMod 49026644363) ^ 17951902 = ((37750831990 : ℕ) : ZMod 49026644363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49026644363 - 1) / 8975951 = 5462 from by norm_num]
      have h2 : (2 : ZMod 49026644363) ^ 5462 = ((42609241018 : ℕ) : ZMod 49026644363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_25624086211087345243 : Nat.Prime 25624086211087345243 := by
  refine lucas_primality 25624086211087345243 (2 : ZMod 25624086211087345243) ?_ (fun q hq hd => ?_)
  · rw [show 25624086211087345243 - 1 = 25624086211087345242 from by norm_num]
    reduce_mod_char
  · have e : 25624086211087345243 - 1 = [2 ^ 1, 3 ^ 3, 9678821 ^ 1, 49026644363 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25624086211087345243 - 1) / 2 = 12812043105543672621 from by norm_num]
      have h2 : (2 : ZMod 25624086211087345243) ^ 12812043105543672621 = ((25624086211087345242 : ℕ) : ZMod 25624086211087345243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25624086211087345243 - 1) / 3 = 8541362070362448414 from by norm_num]
      have h2 : (2 : ZMod 25624086211087345243) ^ 8541362070362448414 = ((16739076802002578919 : ℕ) : ZMod 25624086211087345243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25624086211087345243 - 1) / 9678821 = 2647438795602 from by norm_num]
      have h2 : (2 : ZMod 25624086211087345243) ^ 2647438795602 = ((22116867007706889568 : ℕ) : ZMod 25624086211087345243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_49026644363).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25624086211087345243 - 1) / 49026644363 = 522656334 from by norm_num]
      have h2 : (2 : ZMod 25624086211087345243) ^ 522656334 = ((21116824982932204665 : ℕ) : ZMod 25624086211087345243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1633552383739 : Nat.Prime 1633552383739 := by
  refine lucas_primality 1633552383739 (2 : ZMod 1633552383739) ?_ (fun q hq hd => ?_)
  · rw [show 1633552383739 - 1 = 1633552383738 from by norm_num]
    reduce_mod_char
  · have e : 1633552383739 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 139033 ^ 1, 178021 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1633552383739 - 1) / 2 = 816776191869 from by norm_num]
      have h2 : (2 : ZMod 1633552383739) ^ 816776191869 = ((1633552383738 : ℕ) : ZMod 1633552383739) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1633552383739 - 1) / 3 = 544517461246 from by norm_num]
      have h2 : (2 : ZMod 1633552383739) ^ 544517461246 = ((343936295866 : ℕ) : ZMod 1633552383739) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1633552383739 - 1) / 11 = 148504762158 from by norm_num]
      have h2 : (2 : ZMod 1633552383739) ^ 148504762158 = ((1293107809266 : ℕ) : ZMod 1633552383739) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1633552383739 - 1) / 139033 = 11749386 from by norm_num]
      have h2 : (2 : ZMod 1633552383739) ^ 11749386 = ((569793381299 : ℕ) : ZMod 1633552383739) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1633552383739 - 1) / 178021 = 9176178 from by norm_num]
      have h2 : (2 : ZMod 1633552383739) ^ 9176178 = ((820456104492 : ℕ) : ZMod 1633552383739) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_534366212823606171881874993300544219189772104182089 : Nat.Prime 534366212823606171881874993300544219189772104182089 := by
  refine lucas_primality 534366212823606171881874993300544219189772104182089 (3 : ZMod 534366212823606171881874993300544219189772104182089) ?_ (fun q hq hd => ?_)
  · rw [show 534366212823606171881874993300544219189772104182089 - 1 = 534366212823606171881874993300544219189772104182088 from by norm_num]
    reduce_mod_char
  · have e : 534366212823606171881874993300544219189772104182089 - 1 = [2 ^ 3, 53 ^ 1, 11807 ^ 1, 346441 ^ 1, 7360763 ^ 1, 1633552383739 ^ 1, 25624086211087345243 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (534366212823606171881874993300544219189772104182089 - 1) / 2 = 267183106411803085940937496650272109594886052091044 from by norm_num]
      have h2 : (3 : ZMod 534366212823606171881874993300544219189772104182089) ^ 267183106411803085940937496650272109594886052091044 = ((534366212823606171881874993300544219189772104182088 : ℕ) : ZMod 534366212823606171881874993300544219189772104182089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (534366212823606171881874993300544219189772104182089 - 1) / 53 = 10082381374030305129846697986802721116788152909096 from by norm_num]
      have h2 : (3 : ZMod 534366212823606171881874993300544219189772104182089) ^ 10082381374030305129846697986802721116788152909096 = ((5684341886080801486968994140625 : ℕ) : ZMod 534366212823606171881874993300544219189772104182089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (534366212823606171881874993300544219189772104182089 - 1) / 11807 = 45258424055526905385099940145722386651119852984 from by norm_num]
      have h2 : (3 : ZMod 534366212823606171881874993300544219189772104182089) ^ 45258424055526905385099940145722386651119852984 = ((490652964405609845026646008433461544631403634953857 : ℕ) : ZMod 534366212823606171881874993300544219189772104182089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (534366212823606171881874993300544219189772104182089 - 1) / 346441 = 1542445070946008618731255807772591059342780168 from by norm_num]
      have h2 : (3 : ZMod 534366212823606171881874993300544219189772104182089) ^ 1542445070946008618731255807772591059342780168 = ((115657296409300352301135983183350003429652444684623 : ℕ) : ZMod 534366212823606171881874993300544219189772104182089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (534366212823606171881874993300544219189772104182089 - 1) / 7360763 = 72596579026332755433353171851959398664210776 from by norm_num]
      have h2 : (3 : ZMod 534366212823606171881874993300544219189772104182089) ^ 72596579026332755433353171851959398664210776 = ((482126906421720848315932228560622323614861210206341 : ℕ) : ZMod 534366212823606171881874993300544219189772104182089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1633552383739).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (534366212823606171881874993300544219189772104182089 - 1) / 1633552383739 = 327119116682691126565095433960711067992 from by norm_num]
      have h2 : (3 : ZMod 534366212823606171881874993300544219189772104182089) ^ 327119116682691126565095433960711067992 = ((304636127953479606447052363443805694123629253463718 : ℕ) : ZMod 534366212823606171881874993300544219189772104182089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_25624086211087345243).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (534366212823606171881874993300544219189772104182089 - 1) / 25624086211087345243 = 20854059279288172896265829027416 from by norm_num]
      have h2 : (3 : ZMod 534366212823606171881874993300544219189772104182089) ^ 20854059279288172896265829027416 = ((174843053886138119914558240035511223229524941141002 : ℕ) : ZMod 534366212823606171881874993300544219189772104182089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 106: 7 divides 13 + 1 and 41 + 1 (5^106+1 -> 13; 5^106+1 -> 534366212823606171881874993300544219189772104182089 -> 41).
theorem ke106 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 106 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13 ∣ 1 + 5 ^ 106).trans hd)
  have g534366212823606171881874993300544219189772104182089 : 534366212823606171881874993300544219189772104182089 ∈ P := S7 534366212823606171881874993300544219189772104182089 prime_534366212823606171881874993300544219189772104182089 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 534366212823606171881874993300544219189772104182089 ∣ 1 + 5 ^ 106).trans hd)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 534366212823606171881874993300544219189772104182089 g534366212823606171881874993300544219189772104182089 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 41 g41 (by norm_num) (by norm_num)) (by norm_num)

-- e an odd multiple of 109: 3^2 divides 19403 + 1 (5^109+1 -> 19403).
theorem ke109 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 109 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g19403 : 19403 ∈ P := S7 19403 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 19403 ∣ 1 + 5 ^ 109).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 19403 g19403 (by norm_num)

-- e an odd multiple of 116: 3^2 divides 233 + 1 (5^116+1 -> 233).
theorem ke116 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 116 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g233 : 233 ∈ P := S7 233 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 233 ∣ 1 + 5 ^ 116).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 233 g233 (by norm_num)

theorem prime_13624382047 : Nat.Prime 13624382047 := by
  refine lucas_primality 13624382047 (5 : ZMod 13624382047) ?_ (fun q hq hd => ?_)
  · rw [show 13624382047 - 1 = 13624382046 from by norm_num]
    reduce_mod_char
  · have e : 13624382047 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 17 ^ 1, 691 ^ 1, 17573 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13624382047 - 1) / 2 = 6812191023 from by norm_num]
      have h2 : (5 : ZMod 13624382047) ^ 6812191023 = ((13624382046 : ℕ) : ZMod 13624382047) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13624382047 - 1) / 3 = 4541460682 from by norm_num]
      have h2 : (5 : ZMod 13624382047) ^ 4541460682 = ((115039490 : ℕ) : ZMod 13624382047) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13624382047 - 1) / 11 = 1238580186 from by norm_num]
      have h2 : (5 : ZMod 13624382047) ^ 1238580186 = ((7992711937 : ℕ) : ZMod 13624382047) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13624382047 - 1) / 17 = 801434238 from by norm_num]
      have h2 : (5 : ZMod 13624382047) ^ 801434238 = ((3964373415 : ℕ) : ZMod 13624382047) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13624382047 - 1) / 691 = 19716906 from by norm_num]
      have h2 : (5 : ZMod 13624382047) ^ 19716906 = ((1205512091 : ℕ) : ZMod 13624382047) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13624382047 - 1) / 17573 = 775302 from by norm_num]
      have h2 : (5 : ZMod 13624382047) ^ 775302 = ((13266950218 : ℕ) : ZMod 13624382047) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_22125996444329 : Nat.Prime 22125996444329 := by
  refine lucas_primality 22125996444329 (3 : ZMod 22125996444329) ?_ (fun q hq hd => ?_)
  · rw [show 22125996444329 - 1 = 22125996444328 from by norm_num]
    reduce_mod_char
  · have e : 22125996444329 - 1 = [2 ^ 3, 7 ^ 1, 29 ^ 1, 13624382047 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22125996444329 - 1) / 2 = 11062998222164 from by norm_num]
      have h2 : (3 : ZMod 22125996444329) ^ 11062998222164 = ((22125996444328 : ℕ) : ZMod 22125996444329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22125996444329 - 1) / 7 = 3160856634904 from by norm_num]
      have h2 : (3 : ZMod 22125996444329) ^ 3160856634904 = ((16444877945720 : ℕ) : ZMod 22125996444329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22125996444329 - 1) / 29 = 762965394632 from by norm_num]
      have h2 : (3 : ZMod 22125996444329) ^ 762965394632 = ((8177768285824 : ℕ) : ZMod 22125996444329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_13624382047).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22125996444329 - 1) / 13624382047 = 1624 from by norm_num]
      have h2 : (3 : ZMod 22125996444329) ^ 1624 = ((14385199064677 : ℕ) : ZMod 22125996444329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6090817323763 : Nat.Prime 6090817323763 := by
  refine lucas_primality 6090817323763 (22 : ZMod 6090817323763) ?_ (fun q hq hd => ?_)
  · rw [show 6090817323763 - 1 = 6090817323762 from by norm_num]
    reduce_mod_char
  · have e : 6090817323763 - 1 = [2 ^ 1, 3 ^ 4, 17 ^ 1, 29 ^ 1, 37 ^ 1, 2061161 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6090817323763 - 1) / 2 = 3045408661881 from by norm_num]
      have h2 : (22 : ZMod 6090817323763) ^ 3045408661881 = ((6090817323762 : ℕ) : ZMod 6090817323763) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6090817323763 - 1) / 3 = 2030272441254 from by norm_num]
      have h2 : (22 : ZMod 6090817323763) ^ 2030272441254 = ((1408863766424 : ℕ) : ZMod 6090817323763) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6090817323763 - 1) / 17 = 358283371986 from by norm_num]
      have h2 : (22 : ZMod 6090817323763) ^ 358283371986 = ((53265461126 : ℕ) : ZMod 6090817323763) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6090817323763 - 1) / 29 = 210028183578 from by norm_num]
      have h2 : (22 : ZMod 6090817323763) ^ 210028183578 = ((25 : ℕ) : ZMod 6090817323763) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6090817323763 - 1) / 37 = 164616684426 from by norm_num]
      have h2 : (22 : ZMod 6090817323763) ^ 164616684426 = ((5431581376484 : ℕ) : ZMod 6090817323763) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6090817323763 - 1) / 2061161 = 2955042 from by norm_num]
      have h2 : (22 : ZMod 6090817323763) ^ 2955042 = ((4067609198174 : ℕ) : ZMod 6090817323763) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1157409822348098469384602128957288052006070702052516944254770910797210840078500601 : Nat.Prime 1157409822348098469384602128957288052006070702052516944254770910797210840078500601 := by
  refine lucas_primality 1157409822348098469384602128957288052006070702052516944254770910797210840078500601 (17 : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) ?_ (fun q hq hd => ?_)
  · rw [show 1157409822348098469384602128957288052006070702052516944254770910797210840078500601 - 1 = 1157409822348098469384602128957288052006070702052516944254770910797210840078500600 from by norm_num]
    reduce_mod_char
  · have e : 1157409822348098469384602128957288052006070702052516944254770910797210840078500601 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 2, 59 ^ 1, 35671 ^ 1, 5096867 ^ 1, 6090817323763 ^ 1, 22125996444329 ^ 1, 1334402673828313149547634216455312875601 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1157409822348098469384602128957288052006070702052516944254770910797210840078500601 - 1) / 2 = 578704911174049234692301064478644026003035351026258472127385455398605420039250300 from by norm_num]
      have h2 : (17 : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) ^ 578704911174049234692301064478644026003035351026258472127385455398605420039250300 = ((1157409822348098469384602128957288052006070702052516944254770910797210840078500600 : ℕ) : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1157409822348098469384602128957288052006070702052516944254770910797210840078500601 - 1) / 3 = 385803274116032823128200709652429350668690234017505648084923636932403613359500200 from by norm_num]
      have h2 : (17 : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) ^ 385803274116032823128200709652429350668690234017505648084923636932403613359500200 = ((773705717600528211173493726130215079004166771001517695010358348031292183782770424 : ℕ) : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1157409822348098469384602128957288052006070702052516944254770910797210840078500601 - 1) / 5 = 231481964469619693876920425791457610401214140410503388850954182159442168015700120 from by norm_num]
      have h2 : (17 : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) ^ 231481964469619693876920425791457610401214140410503388850954182159442168015700120 = ((1027078520820398833166059439796473979961836686276355968613827434870476072967729535 : ℕ) : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1157409822348098469384602128957288052006070702052516944254770910797210840078500601 - 1) / 59 = 19617115633018618125162747948428611050950350882246049902623235776223912543703400 from by norm_num]
      have h2 : (17 : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) ^ 19617115633018618125162747948428611050950350882246049902623235776223912543703400 = ((1109261573738417573058202680392664869042618160847132239373772440908046869131234976 : ℕ) : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1157409822348098469384602128957288052006070702052516944254770910797210840078500601 - 1) / 35671 = 32446800548010946409817558491696001009393364415141626089954610490236069638600 from by norm_num]
      have h2 : (17 : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) ^ 32446800548010946409817558491696001009393364415141626089954610490236069638600 = ((646259944139033043615098669342157165917910563494149531108772564147972399103570936 : ℕ) : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1157409822348098469384602128957288052006070702052516944254770910797210840078500601 - 1) / 5096867 = 227082602380658249348982841607852049505327626177515902269918149874660421800 from by norm_num]
      have h2 : (17 : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) ^ 227082602380658249348982841607852049505327626177515902269918149874660421800 = ((991595284197397828445869788381251127262806318337569658699300316263442325942559191 : ℕ) : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6090817323763).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1157409822348098469384602128957288052006070702052516944254770910797210840078500601 - 1) / 6090817323763 = 190025371116044734350188291905219956517547961145711059753711377596200 from by norm_num]
      have h2 : (17 : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) ^ 190025371116044734350188291905219956517547961145711059753711377596200 = ((940405484056904183946587802655690795267095570760076174751279364171749823880189502 : ℕ) : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_22125996444329).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1157409822348098469384602128957288052006070702052516944254770910797210840078500601 - 1) / 22125996444329 = 52309952469722474796853647851427956320200830654312784855182362361400 from by norm_num]
      have h2 : (17 : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) ^ 52309952469722474796853647851427956320200830654312784855182362361400 = ((933445508663112511678876245044474610100255690057900265851754489585244896277489902 : ℕ) : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1334402673828313149547634216455312875601).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1157409822348098469384602128957288052006070702052516944254770910797210840078500601 - 1) / 1334402673828313149547634216455312875601 = 867361737988403547205962240695953369140600 from by norm_num]
      have h2 : (17 : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) ^ 867361737988403547205962240695953369140600 = ((506084256718095968288978516422596844070601537808899892056751865772989367392124507 : ℕ) : ZMod 1157409822348098469384602128957288052006070702052516944254770910797210840078500601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 118: 3 divides 11 + 1 and 2687 + 1 (5^118+1 -> 1157409822348098469384602128957288052006070702052516944254770910797210840078500601 -> 59113 -> 11; 5^118+1 -> 1157409822348098469384602128957288052006070702052516944254770910797210840078500601 -> 59113 -> 2687).
theorem ke118 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 118 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g1157409822348098469384602128957288052006070702052516944254770910797210840078500601 : 1157409822348098469384602128957288052006070702052516944254770910797210840078500601 ∈ P := S7 1157409822348098469384602128957288052006070702052516944254770910797210840078500601 prime_1157409822348098469384602128957288052006070702052516944254770910797210840078500601 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1157409822348098469384602128957288052006070702052516944254770910797210840078500601 ∣ 1 + 5 ^ 118).trans hd)
  have g59113 : 59113 ∈ P := S1 59113 (by norm_num) (by norm_num) (hnz (by norm_num)) 1157409822348098469384602128957288052006070702052516944254770910797210840078500601 g1157409822348098469384602128957288052006070702052516944254770910797210840078500601 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 59113 g59113 (by norm_num)
  have g2687 : 2687 ∈ P := S1 2687 (by norm_num) (by norm_num) (hnz (by norm_num)) 59113 g59113 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 11 g11 2687 g2687 (by norm_num) (by norm_num)) (by norm_num)

-- e an odd multiple of 122: 3^2 divides 61001 + 1 (5^122+1 -> 61001).
theorem ke122 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 122 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g61001 : 61001 ∈ P := S7 61001 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 61001 ∣ 1 + 5 ^ 122).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 61001 g61001 (by norm_num)

theorem prime_23320317172851318360001 : Nat.Prime 23320317172851318360001 := by
  refine lucas_primality 23320317172851318360001 (22 : ZMod 23320317172851318360001) ?_ (fun q hq hd => ?_)
  · rw [show 23320317172851318360001 - 1 = 23320317172851318360000 from by norm_num]
    reduce_mod_char
  · have e : 23320317172851318360001 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 4, 13 ^ 1, 17 ^ 1, 61 ^ 1, 313 ^ 1, 11489 ^ 1, 4008709 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23320317172851318360001 - 1) / 2 = 11660158586425659180000 from by norm_num]
      have h2 : (22 : ZMod 23320317172851318360001) ^ 11660158586425659180000 = ((23320317172851318360000 : ℕ) : ZMod 23320317172851318360001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23320317172851318360001 - 1) / 3 = 7773439057617106120000 from by norm_num]
      have h2 : (22 : ZMod 23320317172851318360001) ^ 7773439057617106120000 = ((23320317077483886719376 : ℕ) : ZMod 23320317172851318360001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23320317172851318360001 - 1) / 5 = 4664063434570263672000 from by norm_num]
      have h2 : (22 : ZMod 23320317172851318360001) ^ 4664063434570263672000 = ((23320317172851074219376 : ℕ) : ZMod 23320317172851318360001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23320317172851318360001 - 1) / 13 = 1793870551757793720000 from by norm_num]
      have h2 : (22 : ZMod 23320317172851318360001) ^ 1793870551757793720000 = ((3649174052162578775775 : ℕ) : ZMod 23320317172851318360001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23320317172851318360001 - 1) / 17 = 1371783363108901080000 from by norm_num]
      have h2 : (22 : ZMod 23320317172851318360001) ^ 1371783363108901080000 = ((11280239816507656053794 : ℕ) : ZMod 23320317172851318360001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23320317172851318360001 - 1) / 61 = 382300281522152760000 from by norm_num]
      have h2 : (22 : ZMod 23320317172851318360001) ^ 382300281522152760000 = ((19370647680628286835461 : ℕ) : ZMod 23320317172851318360001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23320317172851318360001 - 1) / 313 = 74505805664061720000 from by norm_num]
      have h2 : (22 : ZMod 23320317172851318360001) ^ 74505805664061720000 = ((17435519552639491824367 : ℕ) : ZMod 23320317172851318360001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23320317172851318360001 - 1) / 11489 = 2029795210449240000 from by norm_num]
      have h2 : (22 : ZMod 23320317172851318360001) ^ 2029795210449240000 = ((22198440879377058380854 : ℕ) : ZMod 23320317172851318360001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23320317172851318360001 - 1) / 4008709 = 5817413330040000 from by norm_num]
      have h2 : (22 : ZMod 23320317172851318360001) ^ 5817413330040000 = ((17410581889332075786103 : ℕ) : ZMod 23320317172851318360001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_69566521 : Nat.Prime 69566521 := by
  refine lucas_primality 69566521 (7 : ZMod 69566521) ?_ (fun q hq hd => ?_)
  · rw [show 69566521 - 1 = 69566520 from by norm_num]
    reduce_mod_char
  · have e : 69566521 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 579721 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69566521 - 1) / 2 = 34783260 from by norm_num]
      have h2 : (7 : ZMod 69566521) ^ 34783260 = ((69566520 : ℕ) : ZMod 69566521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69566521 - 1) / 3 = 23188840 from by norm_num]
      have h2 : (7 : ZMod 69566521) ^ 23188840 = ((59800896 : ℕ) : ZMod 69566521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69566521 - 1) / 5 = 13913304 from by norm_num]
      have h2 : (7 : ZMod 69566521) ^ 13913304 = ((69550896 : ℕ) : ZMod 69566521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69566521 - 1) / 579721 = 120 from by norm_num]
      have h2 : (7 : ZMod 69566521) ^ 120 = ((4820005 : ℕ) : ZMod 69566521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_751114601164400963558298106851275193494354988352771579238818981647550964507812890001 : Nat.Prime 751114601164400963558298106851275193494354988352771579238818981647550964507812890001 := by
  refine lucas_primality 751114601164400963558298106851275193494354988352771579238818981647550964507812890001 (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ?_ (fun q hq hd => ?_)
  · rw [show 751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1 = 751114601164400963558298106851275193494354988352771579238818981647550964507812890000 from by norm_num]
    reduce_mod_char
  · have e : 751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 4, 7 ^ 1, 11 ^ 1, 13 ^ 1, 31 ^ 1, 41 ^ 1, 61 ^ 1, 71 ^ 1, 181 ^ 1, 241 ^ 1, 521 ^ 1, 601 ^ 1, 1741 ^ 1, 2281 ^ 1, 7621 ^ 1, 9161 ^ 1, 390001 ^ 1, 69566521 ^ 1, 632133361 ^ 1, 23320317172851318360001 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 2 = 375557300582200481779149053425637596747177494176385789619409490823775482253906445000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 375557300582200481779149053425637596747177494176385789619409490823775482253906445000 = ((751114601164400963558298106851275193494354988352771579238818981647550964507812890000 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 3 = 250371533721466987852766035617091731164784996117590526412939660549183654835937630000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 250371533721466987852766035617091731164784996117590526412939660549183654835937630000 = ((368527733691946100581414127208955211343284675328334704663422924451537286274790561668 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 5 = 150222920232880192711659621370255038698870997670554315847763796329510192901562578000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 150222920232880192711659621370255038698870997670554315847763796329510192901562578000 = ((425151413273059815056402706577516931373772555645168596783305148586422382353774631854 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 7 = 107302085880628709079756872407325027642050712621824511319831283092507280643973270000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 107302085880628709079756872407325027642050712621824511319831283092507280643973270000 = ((7521028779776186861341269249724966037640555810596784880408344901375001864362209059 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 11 = 68283145560400087596208918804661381226759544395706507203528998331595542227982990000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 68283145560400087596208918804661381226759544395706507203528998331595542227982990000 = ((256522445301003040498667438436083892234861325899731045032949019794349476439971683535 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 13 = 57778046243415458735253700527021168730334999104059352249139921665196228039062530000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 57778046243415458735253700527021168730334999104059352249139921665196228039062530000 = ((568889238034049884902060978693674632979274018547676146068679390682373537009570876345 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 31 = 24229503263367773018009616350041135274011451237186179975445773601533902080897190000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 24229503263367773018009616350041135274011451237186179975445773601533902080897190000 = ((751114601164400963558298106851275193494354988350551133189568668566703701171631249376 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 41 = 18319868321082950330690197728079882768154999715921258030215097113354901573361290000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 18319868321082950330690197728079882768154999715921258030215097113354901573361290000 = ((118037581755023673912694800193921097657808068763566859583084687445320744530339908166 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 61 = 12313354117449196123906526341824183499907458825455271790800311174550015811603490000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 12313354117449196123906526341824183499907458825455271790800311174550015811603490000 = ((101335254786105993004264842491165495476593042643974819994506571784384427996010979837 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 71 = 10579078889639450190961945166919368922455704061306641961110126502078182598701590000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 10579078889639450190961945166919368922455704061306641961110126502078182598701590000 = ((460036912541915314480107327571807879711216673732059431957061070238369400263915989356 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 181 = 4149804426322657257228166336194890571792016510236307067617784428991994279048690000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 4149804426322657257228166336194890571792016510236307067617784428991994279048690000 = ((620003870779686507998584520816546676659477030304264895032908864862540643809472610333 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 241 = 3116658096117846321818664343781224869271182524285359249953605732977389894223290000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 3116658096117846321818664343781224869271182524285359249953605732977389894223290000 = ((86297697119403498010452323638640205764464232777457938188513509965923383479841256138 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 521 = 1441678697052593020265447421979414958722370419103208405448788832336950027846090000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 1441678697052593020265447421979414958722370419103208405448788832336950027846090000 = ((421671730807482542853611165399751904743871008443664835774660635064737335825299769978 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 601 = 1249774710756074814572875385775832268709409298423912777435638904571632220478890000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 1249774710756074814572875385775832268709409298423912777435638904571632220478890000 = ((15776115090592448489262633230163640688278896163302391416309710358277964341545825420 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 1741 = 431427111524641564364329756950761168003650194343923939827006882049138980188290000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 431427111524641564364329756950761168003650194343923939827006882049138980188290000 = ((521077905608568624131268096269335421426756291832469303140587876590735779735792100874 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 2281 = 329291802351775959473168832464390702978673822162547820797377896382091610919690000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 329291802351775959473168832464390702978673822162547820797377896382091610919690000 = ((217362531464717525100374714379741079981842864878903730713081394231754816830507300100 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 7621 = 98558535778034505125088322641552971197264793118064765678889775836183042187090000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 98558535778034505125088322641552971197264793118064765678889775836183042187090000 = ((77813726993274075925436078545134641239511157469030513443247482089129346900781520226 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 9161 = 81990459683921074506964098553790546173382271406262589153893568567574605884490000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 81990459683921074506964098553790546173382271406262589153893568567574605884490000 = ((68027237279999191213338108187488238568716281812334259006998399427858594023248590064 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 390001 = 1925929936498626833157602433971387748991297428347033928730487823486480712890000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 1925929936498626833157602433971387748991297428347033928730487823486480712890000 = ((529047615329064531488827231106479495421759388553679097544841781225778986896156094751 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_69566521).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 69566521 = 10797070061393482125666426625693632048875277065425933535454776898323706090000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 10797070061393482125666426625693632048875277065425933535454776898323706090000 = ((649608375893463183063653104220402259069486658864410686608735699645775442308282821533 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_632133361).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 632133361 = 1188221738489136572493439571608490369636344803438987582936346530914306490000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 1188221738489136572493439571608490369636344803438987582936346530914306490000 = ((707832942642921773389475277657310871574145856507154862355422655220935859596184548564 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_23320317172851318360001).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (751114601164400963558298106851275193494354988352771579238818981647550964507812890001 - 1) / 23320317172851318360001 = 32208592859055184599338661488587831627228260159206847412890000 from by norm_num]
      have h2 : (19 : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) ^ 32208592859055184599338661488587831627228260159206847412890000 = ((695422258331541789335460619833514887308230594161302684526335561552944958172537112879 : ℕ) : ZMod 751114601164400963558298106851275193494354988352771579238818981647550964507812890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 124: 7^2 divides 97 + 1 (5^124+1 -> 751114601164400963558298106851275193494354988352771579238818981647550964507812890001 -> 193 -> 97).
theorem ke124 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 124 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g751114601164400963558298106851275193494354988352771579238818981647550964507812890001 : 751114601164400963558298106851275193494354988352771579238818981647550964507812890001 ∈ P := S7 751114601164400963558298106851275193494354988352771579238818981647550964507812890001 prime_751114601164400963558298106851275193494354988352771579238818981647550964507812890001 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 751114601164400963558298106851275193494354988352771579238818981647550964507812890001 ∣ 1 + 5 ^ 124).trans hd)
  have g193 : 193 ∈ P := S1 193 (by norm_num) (by norm_num) (hnz (by norm_num)) 751114601164400963558298106851275193494354988352771579238818981647550964507812890001 g751114601164400963558298106851275193494354988352771579238818981647550964507812890001 (by norm_num)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 193 g193 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)

-- e an odd multiple of 127: 3 divides 5^127 + 1 and 509 + 1 (5^127+1 -> 509).
theorem ke127 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 127 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g509 : 509 ∈ P := S7 509 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 509 ∣ 1 + 5 ^ 127).trans hd)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 127).trans hd) 509 g509 (by norm_num)

-- e an odd multiple of 128: 3 divides 257 + 1 and 11 + 1 (5^128+1 -> 257; 5^128+1 -> 257 -> 43 -> 11).
theorem ke128 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 128 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g257 : 257 ∈ P := S7 257 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 257 ∣ 1 + 5 ^ 128).trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 11 g11 (by norm_num) (by norm_num)) (by norm_num)

-- e an odd multiple of 134: 7^2 divides 97 + 1 (5^134+1 -> 20369 -> 97).
theorem ke134 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 134 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g20369 : 20369 ∈ P := S7 20369 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 20369 ∣ 1 + 5 ^ 134).trans hd)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 20369 g20369 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)

theorem prime_172694671812043 : Nat.Prime 172694671812043 := by
  refine lucas_primality 172694671812043 (2 : ZMod 172694671812043) ?_ (fun q hq hd => ?_)
  · rw [show 172694671812043 - 1 = 172694671812042 from by norm_num]
    reduce_mod_char
  · have e : 172694671812043 - 1 = [2 ^ 1, 3 ^ 1, 139 ^ 1, 62563 ^ 1, 3309751 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (172694671812043 - 1) / 2 = 86347335906021 from by norm_num]
      have h2 : (2 : ZMod 172694671812043) ^ 86347335906021 = ((172694671812042 : ℕ) : ZMod 172694671812043) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (172694671812043 - 1) / 3 = 57564890604014 from by norm_num]
      have h2 : (2 : ZMod 172694671812043) ^ 57564890604014 = ((81344825421415 : ℕ) : ZMod 172694671812043) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (172694671812043 - 1) / 139 = 1242407710878 from by norm_num]
      have h2 : (2 : ZMod 172694671812043) ^ 1242407710878 = ((76951616713906 : ℕ) : ZMod 172694671812043) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (172694671812043 - 1) / 62563 = 2760332334 from by norm_num]
      have h2 : (2 : ZMod 172694671812043) ^ 2760332334 = ((24031715463707 : ℕ) : ZMod 172694671812043) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (172694671812043 - 1) / 3309751 = 52177542 from by norm_num]
      have h2 : (2 : ZMod 172694671812043) ^ 52177542 = ((23658126188287 : ℕ) : ZMod 172694671812043) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 139: 3 divides 5^139 + 1 and 23 + 1 (5^139+1 -> 172694671812043 -> 23).
theorem ke139 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 139 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g172694671812043 : 172694671812043 ∈ P := S7 172694671812043 prime_172694671812043 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 172694671812043 ∣ 1 + 5 ^ 139).trans hd)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 172694671812043 g172694671812043 (by norm_num)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 139).trans hd) 23 g23 (by norm_num)

-- e an odd multiple of 142: 7 divides 13 + 1 and 853 + 1 (5^142+1 -> 13; 5^142+1 -> 853).
theorem ke142 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 142 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13 ∣ 1 + 5 ^ 142).trans hd)
  have g853 : 853 ∈ P := S7 853 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 853 ∣ 1 + 5 ^ 142).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 853 g853 (by norm_num) (by norm_num)) (by norm_num)

-- e an odd multiple of 146: 7^2 divides 293 + 1 (5^146+1 -> 293).
theorem ke146 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 146 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g293 : 293 ∈ P := S7 293 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 293 ∣ 1 + 5 ^ 146).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 293 g293 (by norm_num)

-- e an odd multiple of 148: 3^2 divides 3257 + 1 (5^148+1 -> 3257).
theorem ke148 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 148 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g3257 : 3257 ∈ P := S7 3257 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3257 ∣ 1 + 5 ^ 148).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 3257 g3257 (by norm_num)

theorem prime_43367201 : Nat.Prime 43367201 := by
  refine lucas_primality 43367201 (3 : ZMod 43367201) ?_ (fun q hq hd => ?_)
  · rw [show 43367201 - 1 = 43367200 from by norm_num]
    reduce_mod_char
  · have e : 43367201 - 1 = [2 ^ 5, 5 ^ 2, 151 ^ 1, 359 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43367201 - 1) / 2 = 21683600 from by norm_num]
      have h2 : (3 : ZMod 43367201) ^ 21683600 = ((43367200 : ℕ) : ZMod 43367201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43367201 - 1) / 5 = 8673440 from by norm_num]
      have h2 : (3 : ZMod 43367201) ^ 8673440 = ((23339478 : ℕ) : ZMod 43367201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43367201 - 1) / 151 = 287200 from by norm_num]
      have h2 : (3 : ZMod 43367201) ^ 287200 = ((5185803 : ℕ) : ZMod 43367201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43367201 - 1) / 359 = 120800 from by norm_num]
      have h2 : (3 : ZMod 43367201) ^ 120800 = ((585162 : ℕ) : ZMod 43367201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 151: 3^2 divides 43367201 + 1 (5^151+1 -> 43367201).
theorem ke151 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 151 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g43367201 : 43367201 ∈ P := S7 43367201 prime_43367201 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43367201 ∣ 1 + 5 ^ 151).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 43367201 g43367201 (by norm_num)

-- e an odd multiple of 157: 3 divides 5^157 + 1 and 41 + 1 (5^157+1 -> 1585387 -> 41).
theorem ke157 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 157 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g1585387 : 1585387 ∈ P := S7 1585387 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1585387 ∣ 1 + 5 ^ 157).trans hd)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 1585387 g1585387 (by norm_num)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 157).trans hd) 41 g41 (by norm_num)

-- e an odd multiple of 158: 3^2 divides 53 + 1 (5^158+1 -> 317 -> 53).
theorem ke158 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 158 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g317 : 317 ∈ P := S7 317 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 317 ∣ 1 + 5 ^ 158).trans hd)
  have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 317 g317 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 53 g53 (by norm_num)

theorem prime_1670043928229 : Nat.Prime 1670043928229 := by
  refine lucas_primality 1670043928229 (2 : ZMod 1670043928229) ?_ (fun q hq hd => ?_)
  · rw [show 1670043928229 - 1 = 1670043928228 from by norm_num]
    reduce_mod_char
  · have e : 1670043928229 - 1 = [2 ^ 2, 13 ^ 1, 59 ^ 1, 71 ^ 1, 389 ^ 1, 19709 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1670043928229 - 1) / 2 = 835021964114 from by norm_num]
      have h2 : (2 : ZMod 1670043928229) ^ 835021964114 = ((1670043928228 : ℕ) : ZMod 1670043928229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1670043928229 - 1) / 13 = 128464917556 from by norm_num]
      have h2 : (2 : ZMod 1670043928229) ^ 128464917556 = ((677824879241 : ℕ) : ZMod 1670043928229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1670043928229 - 1) / 59 = 28305829292 from by norm_num]
      have h2 : (2 : ZMod 1670043928229) ^ 28305829292 = ((1548323259150 : ℕ) : ZMod 1670043928229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1670043928229 - 1) / 71 = 23521745468 from by norm_num]
      have h2 : (2 : ZMod 1670043928229) ^ 23521745468 = ((477895285369 : ℕ) : ZMod 1670043928229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1670043928229 - 1) / 389 = 4293172052 from by norm_num]
      have h2 : (2 : ZMod 1670043928229) ^ 4293172052 = ((389049276322 : ℕ) : ZMod 1670043928229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1670043928229 - 1) / 19709 = 84735092 from by norm_num]
      have h2 : (2 : ZMod 1670043928229) ^ 84735092 = ((953823459535 : ℕ) : ZMod 1670043928229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1981740926993660561 : Nat.Prime 1981740926993660561 := by
  refine lucas_primality 1981740926993660561 (3 : ZMod 1981740926993660561) ?_ (fun q hq hd => ?_)
  · rw [show 1981740926993660561 - 1 = 1981740926993660560 from by norm_num]
    reduce_mod_char
  · have e : 1981740926993660561 - 1 = [2 ^ 4, 5 ^ 1, 7 ^ 1, 13 ^ 1, 163 ^ 1, 1670043928229 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1981740926993660561 - 1) / 2 = 990870463496830280 from by norm_num]
      have h2 : (3 : ZMod 1981740926993660561) ^ 990870463496830280 = ((1981740926993660560 : ℕ) : ZMod 1981740926993660561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1981740926993660561 - 1) / 5 = 396348185398732112 from by norm_num]
      have h2 : (3 : ZMod 1981740926993660561) ^ 396348185398732112 = ((354454662950057659 : ℕ) : ZMod 1981740926993660561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1981740926993660561 - 1) / 7 = 283105846713380080 from by norm_num]
      have h2 : (3 : ZMod 1981740926993660561) ^ 283105846713380080 = ((1585594739015195899 : ℕ) : ZMod 1981740926993660561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1981740926993660561 - 1) / 13 = 152441609768743120 from by norm_num]
      have h2 : (3 : ZMod 1981740926993660561) ^ 152441609768743120 = ((1447919811067216151 : ℕ) : ZMod 1981740926993660561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1981740926993660561 - 1) / 163 = 12157919797507120 from by norm_num]
      have h2 : (3 : ZMod 1981740926993660561) ^ 12157919797507120 = ((572880975379675676 : ℕ) : ZMod 1981740926993660561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1670043928229).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1981740926993660561 - 1) / 1670043928229 = 1186640 from by norm_num]
      have h2 : (3 : ZMod 1981740926993660561) ^ 1186640 = ((459826307858628338 : ℕ) : ZMod 1981740926993660561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 163: 3 divides 5^163 + 1 and 1981740926993660561 + 1 (5^163+1 -> 1981740926993660561).
theorem ke163 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 163 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g1981740926993660561 : 1981740926993660561 ∈ P := S7 1981740926993660561 prime_1981740926993660561 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1981740926993660561 ∣ 1 + 5 ^ 163).trans hd)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 163).trans hd) 1981740926993660561 g1981740926993660561 (by norm_num)

-- e an odd multiple of 164: 3^2 divides 53 + 1 (5^164+1 -> 2953 -> 211 -> 53).
theorem ke164 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 164 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g2953 : 2953 ∈ P := S7 2953 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2953 ∣ 1 + 5 ^ 164).trans hd)
  have g211 : 211 ∈ P := S1 211 (by norm_num) (by norm_num) (hnz (by norm_num)) 2953 g2953 (by norm_num)
  have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 211 g211 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 53 g53 (by norm_num)

theorem prime_381674287 : Nat.Prime 381674287 := by
  refine lucas_primality 381674287 (3 : ZMod 381674287) ?_ (fun q hq hd => ?_)
  · rw [show 381674287 - 1 = 381674286 from by norm_num]
    reduce_mod_char
  · have e : 381674287 - 1 = [2 ^ 1, 3 ^ 2, 7 ^ 1, 739 ^ 1, 4099 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381674287 - 1) / 2 = 190837143 from by norm_num]
      have h2 : (3 : ZMod 381674287) ^ 190837143 = ((381674286 : ℕ) : ZMod 381674287) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381674287 - 1) / 3 = 127224762 from by norm_num]
      have h2 : (3 : ZMod 381674287) ^ 127224762 = ((134794424 : ℕ) : ZMod 381674287) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381674287 - 1) / 7 = 54524898 from by norm_num]
      have h2 : (3 : ZMod 381674287) ^ 54524898 = ((172852495 : ℕ) : ZMod 381674287) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381674287 - 1) / 739 = 516474 from by norm_num]
      have h2 : (3 : ZMod 381674287) ^ 516474 = ((53074485 : ℕ) : ZMod 381674287) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381674287 - 1) / 4099 = 93114 from by norm_num]
      have h2 : (3 : ZMod 381674287) ^ 93114 = ((205987772 : ℕ) : ZMod 381674287) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8660380409173501 : Nat.Prime 8660380409173501 := by
  refine lucas_primality 8660380409173501 (13 : ZMod 8660380409173501) ?_ (fun q hq hd => ?_)
  · rw [show 8660380409173501 - 1 = 8660380409173500 from by norm_num]
    reduce_mod_char
  · have e : 8660380409173501 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 3, 7 ^ 1, 2161 ^ 1, 381674287 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8660380409173501 - 1) / 2 = 4330190204586750 from by norm_num]
      have h2 : (13 : ZMod 8660380409173501) ^ 4330190204586750 = ((8660380409173500 : ℕ) : ZMod 8660380409173501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8660380409173501 - 1) / 3 = 2886793469724500 from by norm_num]
      have h2 : (13 : ZMod 8660380409173501) ^ 2886793469724500 = ((7554511689629122 : ℕ) : ZMod 8660380409173501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8660380409173501 - 1) / 5 = 1732076081834700 from by norm_num]
      have h2 : (13 : ZMod 8660380409173501) ^ 1732076081834700 = ((6737486039161362 : ℕ) : ZMod 8660380409173501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8660380409173501 - 1) / 7 = 1237197201310500 from by norm_num]
      have h2 : (13 : ZMod 8660380409173501) ^ 1237197201310500 = ((7654526088005975 : ℕ) : ZMod 8660380409173501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8660380409173501 - 1) / 2161 = 4007580013500 from by norm_num]
      have h2 : (13 : ZMod 8660380409173501) ^ 4007580013500 = ((7191353295210011 : ℕ) : ZMod 8660380409173501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_381674287).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8660380409173501 - 1) / 381674287 = 22690500 from by norm_num]
      have h2 : (13 : ZMod 8660380409173501) ^ 22690500 = ((4349234269375350 : ℕ) : ZMod 8660380409173501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_99006230951147470700089 : Nat.Prime 99006230951147470700089 := by
  refine lucas_primality 99006230951147470700089 (11 : ZMod 99006230951147470700089) ?_ (fun q hq hd => ?_)
  · rw [show 99006230951147470700089 - 1 = 99006230951147470700088 from by norm_num]
    reduce_mod_char
  · have e : 99006230951147470700089 - 1 = [2 ^ 3, 3 ^ 2, 83 ^ 1, 1913 ^ 1, 8660380409173501 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99006230951147470700089 - 1) / 2 = 49503115475573735350044 from by norm_num]
      have h2 : (11 : ZMod 99006230951147470700089) ^ 49503115475573735350044 = ((99006230951147470700088 : ℕ) : ZMod 99006230951147470700089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99006230951147470700089 - 1) / 3 = 33002076983715823566696 from by norm_num]
      have h2 : (11 : ZMod 99006230951147470700089) ^ 33002076983715823566696 = ((62232407938673707139315 : ℕ) : ZMod 99006230951147470700089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99006230951147470700089 - 1) / 83 = 1192846156037921333736 from by norm_num]
      have h2 : (11 : ZMod 99006230951147470700089) ^ 1192846156037921333736 = ((95275661256650697298523 : ℕ) : ZMod 99006230951147470700089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99006230951147470700089 - 1) / 1913 = 51754433325220841976 from by norm_num]
      have h2 : (11 : ZMod 99006230951147470700089) ^ 51754433325220841976 = ((89555028146789589784823 : ℕ) : ZMod 99006230951147470700089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_8660380409173501).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99006230951147470700089 - 1) / 8660380409173501 = 11432088 from by norm_num]
      have h2 : (11 : ZMod 99006230951147470700089) ^ 11432088 = ((59859976961027870225510 : ℕ) : ZMod 99006230951147470700089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 166: 11^2 divides 99006230951147470700089 + 1 (5^166+1 -> 99006230951147470700089).
theorem ke166 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 166 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g99006230951147470700089 : 99006230951147470700089 ∈ P := S7 99006230951147470700089 prime_99006230951147470700089 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 99006230951147470700089 ∣ 1 + 5 ^ 166).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 99006230951147470700089 g99006230951147470700089 (by norm_num)

-- e an odd multiple of 172: 3^2 divides 18233 + 1 (5^172+1 -> 18233).
theorem ke172 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 172 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g18233 : 18233 ∈ P := S7 18233 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 18233 ∣ 1 + 5 ^ 172).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 18233 g18233 (by norm_num)

theorem prime_12655250261 : Nat.Prime 12655250261 := by
  refine lucas_primality 12655250261 (2 : ZMod 12655250261) ?_ (fun q hq hd => ?_)
  · rw [show 12655250261 - 1 = 12655250260 from by norm_num]
    reduce_mod_char
  · have e : 12655250261 - 1 = [2 ^ 2, 5 ^ 1, 29 ^ 2, 269 ^ 1, 2797 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12655250261 - 1) / 2 = 6327625130 from by norm_num]
      have h2 : (2 : ZMod 12655250261) ^ 6327625130 = ((12655250260 : ℕ) : ZMod 12655250261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12655250261 - 1) / 5 = 2531050052 from by norm_num]
      have h2 : (2 : ZMod 12655250261) ^ 2531050052 = ((10065198820 : ℕ) : ZMod 12655250261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12655250261 - 1) / 29 = 436387940 from by norm_num]
      have h2 : (2 : ZMod 12655250261) ^ 436387940 = ((12068385097 : ℕ) : ZMod 12655250261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12655250261 - 1) / 269 = 47045540 from by norm_num]
      have h2 : (2 : ZMod 12655250261) ^ 47045540 = ((8641100839 : ℕ) : ZMod 12655250261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12655250261 - 1) / 2797 = 4524580 from by norm_num]
      have h2 : (2 : ZMod 12655250261) ^ 4524580 = ((3135684261 : ℕ) : ZMod 12655250261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_588469137136501 : Nat.Prime 588469137136501 := by
  refine lucas_primality 588469137136501 (6 : ZMod 588469137136501) ?_ (fun q hq hd => ?_)
  · rw [show 588469137136501 - 1 = 588469137136500 from by norm_num]
    reduce_mod_char
  · have e : 588469137136501 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 3, 31 ^ 1, 12655250261 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (588469137136501 - 1) / 2 = 294234568568250 from by norm_num]
      have h2 : (6 : ZMod 588469137136501) ^ 294234568568250 = ((588469137136500 : ℕ) : ZMod 588469137136501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (588469137136501 - 1) / 3 = 196156379045500 from by norm_num]
      have h2 : (6 : ZMod 588469137136501) ^ 196156379045500 = ((384884521562792 : ℕ) : ZMod 588469137136501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (588469137136501 - 1) / 5 = 117693827427300 from by norm_num]
      have h2 : (6 : ZMod 588469137136501) ^ 117693827427300 = ((347556772795951 : ℕ) : ZMod 588469137136501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (588469137136501 - 1) / 31 = 18982875391500 from by norm_num]
      have h2 : (6 : ZMod 588469137136501) ^ 18982875391500 = ((49338928816868 : ℕ) : ZMod 588469137136501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_12655250261).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (588469137136501 - 1) / 12655250261 = 46500 from by norm_num]
      have h2 : (6 : ZMod 588469137136501) ^ 46500 = ((152333953194479 : ℕ) : ZMod 588469137136501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_50816167 : Nat.Prime 50816167 := by
  refine lucas_primality 50816167 (3 : ZMod 50816167) ?_ (fun q hq hd => ?_)
  · rw [show 50816167 - 1 = 50816166 from by norm_num]
    reduce_mod_char
  · have e : 50816167 - 1 = [2 ^ 1, 3 ^ 1, 97 ^ 1, 87313 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50816167 - 1) / 2 = 25408083 from by norm_num]
      have h2 : (3 : ZMod 50816167) ^ 25408083 = ((50816166 : ℕ) : ZMod 50816167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50816167 - 1) / 3 = 16938722 from by norm_num]
      have h2 : (3 : ZMod 50816167) ^ 16938722 = ((7208017 : ℕ) : ZMod 50816167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50816167 - 1) / 97 = 523878 from by norm_num]
      have h2 : (3 : ZMod 50816167) ^ 523878 = ((481398 : ℕ) : ZMod 50816167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50816167 - 1) / 87313 = 582 from by norm_num]
      have h2 : (3 : ZMod 50816167) ^ 582 = ((6373882 : ℕ) : ZMod 50816167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_20365288294844141313970353677 : Nat.Prime 20365288294844141313970353677 := by
  refine lucas_primality 20365288294844141313970353677 (2 : ZMod 20365288294844141313970353677) ?_ (fun q hq hd => ?_)
  · rw [show 20365288294844141313970353677 - 1 = 20365288294844141313970353676 from by norm_num]
    reduce_mod_char
  · have e : 20365288294844141313970353677 - 1 = [2 ^ 2, 89 ^ 1, 1913 ^ 1, 50816167 ^ 1, 588469137136501 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20365288294844141313970353677 - 1) / 2 = 10182644147422070656985176838 from by norm_num]
      have h2 : (2 : ZMod 20365288294844141313970353677) ^ 10182644147422070656985176838 = ((20365288294844141313970353676 : ℕ) : ZMod 20365288294844141313970353677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20365288294844141313970353677 - 1) / 89 = 228823463987012823752475884 from by norm_num]
      have h2 : (2 : ZMod 20365288294844141313970353677) ^ 228823463987012823752475884 = ((8995401727523088936777261220 : ℕ) : ZMod 20365288294844141313970353677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20365288294844141313970353677 - 1) / 1913 = 10645733557158463833753452 from by norm_num]
      have h2 : (2 : ZMod 20365288294844141313970353677) ^ 10645733557158463833753452 = ((13266104483202116309615710173 : ℕ) : ZMod 20365288294844141313970353677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_50816167).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20365288294844141313970353677 - 1) / 50816167 = 400763959525797003028 from by norm_num]
      have h2 : (2 : ZMod 20365288294844141313970353677) ^ 400763959525797003028 = ((129965845204208380655224241 : ℕ) : ZMod 20365288294844141313970353677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_588469137136501).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20365288294844141313970353677 - 1) / 588469137136501 = 34607232579676 from by norm_num]
      have h2 : (2 : ZMod 20365288294844141313970353677) ^ 34607232579676 = ((17582511273148756372003327639 : ℕ) : ZMod 20365288294844141313970353677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 178: 3^2 divides 20365288294844141313970353677 + 1 (5^178+1 -> 20365288294844141313970353677).
theorem ke178 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 178 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g20365288294844141313970353677 : 20365288294844141313970353677 ∈ P := S7 20365288294844141313970353677 prime_20365288294844141313970353677 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 20365288294844141313970353677 ∣ 1 + 5 ^ 178).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 20365288294844141313970353677 g20365288294844141313970353677 (by norm_num)

-- e an odd multiple of 181: 3^2 divides 28961 + 1 (5^181+1 -> 28961).
theorem ke181 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 181 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g28961 : 28961 ∈ P := S7 28961 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 28961 ∣ 1 + 5 ^ 181).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 28961 g28961 (by norm_num)

-- e an odd multiple of 188: 3^2 divides 755009 + 1 (5^188+1 -> 755009).
theorem ke188 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 188 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g755009 : 755009 ∈ P := S7 755009 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 755009 ∣ 1 + 5 ^ 188).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 755009 g755009 (by norm_num)

-- e an odd multiple of 193: 13^2 divides 1046447 + 1 (5^193+1 -> 1046447).
theorem ke193 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 193 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g1046447 : 1046447 ∈ P := S7 1046447 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1046447 ∣ 1 + 5 ^ 193).trans hd)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1046447 g1046447 (by norm_num)

-- e an odd multiple of 194: 3 divides 25997 + 1 and 52769 + 1 (5^194+1 -> 25997; 5^194+1 -> 52769).
theorem ke194 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 194 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g25997 : 25997 ∈ P := S7 25997 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 25997 ∣ 1 + 5 ^ 194).trans hd)
  have g52769 : 52769 ∈ P := S7 52769 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 52769 ∣ 1 + 5 ^ 194).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 25997 g25997 52769 g52769 (by norm_num) (by norm_num)) (by norm_num)

-- e an odd multiple of 199: 3 divides 5^199 + 1 and 239 + 1 (5^199+1 -> 2389 -> 239).
theorem ke199 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 199 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g2389 : 2389 ∈ P := S7 2389 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2389 ∣ 1 + 5 ^ 199).trans hd)
  have g239 : 239 ∈ P := S1 239 (by norm_num) (by norm_num) (hnz (by norm_num)) 2389 g2389 (by norm_num)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 199).trans hd) 239 g239 (by norm_num)

-- e an odd multiple of 202: 3^2 divides 809 + 1 (5^202+1 -> 809).
theorem ke202 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 202 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g809 : 809 ∈ P := S7 809 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 809 ∣ 1 + 5 ^ 202).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 809 g809 (by norm_num)

theorem prime_292327177 : Nat.Prime 292327177 := by
  refine lucas_primality 292327177 (10 : ZMod 292327177) ?_ (fun q hq hd => ?_)
  · rw [show 292327177 - 1 = 292327176 from by norm_num]
    reduce_mod_char
  · have e : 292327177 - 1 = [2 ^ 3, 3 ^ 1, 79 ^ 1, 154181 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292327177 - 1) / 2 = 146163588 from by norm_num]
      have h2 : (10 : ZMod 292327177) ^ 146163588 = ((292327176 : ℕ) : ZMod 292327177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292327177 - 1) / 3 = 97442392 from by norm_num]
      have h2 : (10 : ZMod 292327177) ^ 97442392 = ((194939151 : ℕ) : ZMod 292327177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292327177 - 1) / 79 = 3700344 from by norm_num]
      have h2 : (10 : ZMod 292327177) ^ 3700344 = ((91279261 : ℕ) : ZMod 292327177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292327177 - 1) / 154181 = 1896 from by norm_num]
      have h2 : (10 : ZMod 292327177) ^ 1896 = ((83628455 : ℕ) : ZMod 292327177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_246627708201467263883 : Nat.Prime 246627708201467263883 := by
  refine lucas_primality 246627708201467263883 (2 : ZMod 246627708201467263883) ?_ (fun q hq hd => ?_)
  · rw [show 246627708201467263883 - 1 = 246627708201467263882 from by norm_num]
    reduce_mod_char
  · have e : 246627708201467263883 - 1 = [2 ^ 1, 59 ^ 1, 3089 ^ 1, 2314583 ^ 1, 292327177 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (246627708201467263883 - 1) / 2 = 123313854100733631941 from by norm_num]
      have h2 : (2 : ZMod 246627708201467263883) ^ 123313854100733631941 = ((246627708201467263882 : ℕ) : ZMod 246627708201467263883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (246627708201467263883 - 1) / 59 = 4180130647482495998 from by norm_num]
      have h2 : (2 : ZMod 246627708201467263883) ^ 4180130647482495998 = ((98261531433122909354 : ℕ) : ZMod 246627708201467263883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (246627708201467263883 - 1) / 3089 = 79840630690018538 from by norm_num]
      have h2 : (2 : ZMod 246627708201467263883) ^ 79840630690018538 = ((74883519078041328559 : ℕ) : ZMod 246627708201467263883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (246627708201467263883 - 1) / 2314583 = 106553840670854 from by norm_num]
      have h2 : (2 : ZMod 246627708201467263883) ^ 106553840670854 = ((103742731824316113761 : ℕ) : ZMod 246627708201467263883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_292327177).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (246627708201467263883 - 1) / 292327177 = 843670132666 from by norm_num]
      have h2 : (2 : ZMod 246627708201467263883) ^ 843670132666 = ((110507263551118299617 : ℕ) : ZMod 246627708201467263883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_234105013 : Nat.Prime 234105013 := by
  refine lucas_primality 234105013 (2 : ZMod 234105013) ?_ (fun q hq hd => ?_)
  · rw [show 234105013 - 1 = 234105012 from by norm_num]
    reduce_mod_char
  · have e : 234105013 - 1 = [2 ^ 2, 3 ^ 3, 349 ^ 1, 6211 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234105013 - 1) / 2 = 117052506 from by norm_num]
      have h2 : (2 : ZMod 234105013) ^ 117052506 = ((234105012 : ℕ) : ZMod 234105013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234105013 - 1) / 3 = 78035004 from by norm_num]
      have h2 : (2 : ZMod 234105013) ^ 78035004 = ((67660089 : ℕ) : ZMod 234105013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234105013 - 1) / 349 = 670788 from by norm_num]
      have h2 : (2 : ZMod 234105013) ^ 670788 = ((73696990 : ℕ) : ZMod 234105013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234105013 - 1) / 6211 = 37692 from by norm_num]
      have h2 : (2 : ZMod 234105013) ^ 37692 = ((114854730 : ℕ) : ZMod 234105013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_331492698409 : Nat.Prime 331492698409 := by
  refine lucas_primality 331492698409 (7 : ZMod 331492698409) ?_ (fun q hq hd => ?_)
  · rw [show 331492698409 - 1 = 331492698408 from by norm_num]
    reduce_mod_char
  · have e : 331492698409 - 1 = [2 ^ 3, 3 ^ 1, 59 ^ 1, 234105013 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (331492698409 - 1) / 2 = 165746349204 from by norm_num]
      have h2 : (7 : ZMod 331492698409) ^ 165746349204 = ((331492698408 : ℕ) : ZMod 331492698409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (331492698409 - 1) / 3 = 110497566136 from by norm_num]
      have h2 : (7 : ZMod 331492698409) ^ 110497566136 = ((18600073180 : ℕ) : ZMod 331492698409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (331492698409 - 1) / 59 = 5618520312 from by norm_num]
      have h2 : (7 : ZMod 331492698409) ^ 5618520312 = ((330084001512 : ℕ) : ZMod 331492698409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_234105013).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (331492698409 - 1) / 234105013 = 1416 from by norm_num]
      have h2 : (7 : ZMod 331492698409) ^ 1416 = ((8107863999 : ℕ) : ZMod 331492698409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3977912380909 : Nat.Prime 3977912380909 := by
  refine lucas_primality 3977912380909 (2 : ZMod 3977912380909) ?_ (fun q hq hd => ?_)
  · rw [show 3977912380909 - 1 = 3977912380908 from by norm_num]
    reduce_mod_char
  · have e : 3977912380909 - 1 = [2 ^ 2, 3 ^ 1, 331492698409 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3977912380909 - 1) / 2 = 1988956190454 from by norm_num]
      have h2 : (2 : ZMod 3977912380909) ^ 1988956190454 = ((3977912380908 : ℕ) : ZMod 3977912380909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3977912380909 - 1) / 3 = 1325970793636 from by norm_num]
      have h2 : (2 : ZMod 3977912380909) ^ 1325970793636 = ((1800437328398 : ℕ) : ZMod 3977912380909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_331492698409).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3977912380909 - 1) / 331492698409 = 12 from by norm_num]
      have h2 : (2 : ZMod 3977912380909) ^ 12 = ((4096 : ℕ) : ZMod 3977912380909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7018527663253994876928011333286614639 : Nat.Prime 7018527663253994876928011333286614639 := by
  refine lucas_primality 7018527663253994876928011333286614639 (7 : ZMod 7018527663253994876928011333286614639) ?_ (fun q hq hd => ?_)
  · rw [show 7018527663253994876928011333286614639 - 1 = 7018527663253994876928011333286614638 from by norm_num]
    reduce_mod_char
  · have e : 7018527663253994876928011333286614639 - 1 = [2 ^ 1, 7 ^ 2, 73 ^ 1, 3977912380909 ^ 1, 246627708201467263883 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7018527663253994876928011333286614639 - 1) / 2 = 3509263831626997438464005666643307319 from by norm_num]
      have h2 : (7 : ZMod 7018527663253994876928011333286614639) ^ 3509263831626997438464005666643307319 = ((7018527663253994876928011333286614638 : ℕ) : ZMod 7018527663253994876928011333286614639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7018527663253994876928011333286614639 - 1) / 7 = 1002646809036284982418287333326659234 from by norm_num]
      have h2 : (7 : ZMod 7018527663253994876928011333286614639) ^ 1002646809036284982418287333326659234 = ((2541435835638619921347212708206945593 : ℕ) : ZMod 7018527663253994876928011333286614639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7018527663253994876928011333286614639 - 1) / 73 = 96144214565123217492164538812145406 from by norm_num]
      have h2 : (7 : ZMod 7018527663253994876928011333286614639) ^ 96144214565123217492164538812145406 = ((6875421005057129833007685990942785931 : ℕ) : ZMod 7018527663253994876928011333286614639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3977912380909).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7018527663253994876928011333286614639 - 1) / 3977912380909 = 1764374624473296805818982 from by norm_num]
      have h2 : (7 : ZMod 7018527663253994876928011333286614639) ^ 1764374624473296805818982 = ((859291882195139030031826409227669350 : ℕ) : ZMod 7018527663253994876928011333286614639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_246627708201467263883).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7018527663253994876928011333286614639 - 1) / 246627708201467263883 = 28457985173022986 from by norm_num]
      have h2 : (7 : ZMod 7018527663253994876928011333286614639) ^ 28457985173022986 = ((3062566311649647158128134294408419523 : ℕ) : ZMod 7018527663253994876928011333286614639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_720016715917900826434290826659207222585733 : Nat.Prime 720016715917900826434290826659207222585733 := by
  refine lucas_primality 720016715917900826434290826659207222585733 (2 : ZMod 720016715917900826434290826659207222585733) ?_ (fun q hq hd => ?_)
  · rw [show 720016715917900826434290826659207222585733 - 1 = 720016715917900826434290826659207222585732 from by norm_num]
    reduce_mod_char
  · have e : 720016715917900826434290826659207222585733 - 1 = [2 ^ 2, 3 ^ 1, 83 ^ 1, 103 ^ 1, 7018527663253994876928011333286614639 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (720016715917900826434290826659207222585733 - 1) / 2 = 360008357958950413217145413329603611292866 from by norm_num]
      have h2 : (2 : ZMod 720016715917900826434290826659207222585733) ^ 360008357958950413217145413329603611292866 = ((720016715917900826434290826659207222585732 : ℕ) : ZMod 720016715917900826434290826659207222585733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (720016715917900826434290826659207222585733 - 1) / 3 = 240005571972633608811430275553069074195244 from by norm_num]
      have h2 : (2 : ZMod 720016715917900826434290826659207222585733) ^ 240005571972633608811430275553069074195244 = ((435363189499780954937494857237771935796389 : ℕ) : ZMod 720016715917900826434290826659207222585733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (720016715917900826434290826659207222585733 - 1) / 83 = 8674900191781937667883022007942255693804 from by norm_num]
      have h2 : (2 : ZMod 720016715917900826434290826659207222585733) ^ 8674900191781937667883022007942255693804 = ((94629021294014738055365079197185305299416 : ℕ) : ZMod 720016715917900826434290826659207222585733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (720016715917900826434290826659207222585733 - 1) / 103 = 6990453552600978897420299287953468180444 from by norm_num]
      have h2 : (2 : ZMod 720016715917900826434290826659207222585733) ^ 6990453552600978897420299287953468180444 = ((219810934467058615211930967356401578056861 : ℕ) : ZMod 720016715917900826434290826659207222585733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_7018527663253994876928011333286614639).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (720016715917900826434290826659207222585733 - 1) / 7018527663253994876928011333286614639 = 102588 from by norm_num]
      have h2 : (2 : ZMod 720016715917900826434290826659207222585733) ^ 102588 = ((266673273175454417569926870832769045138513 : ℕ) : ZMod 720016715917900826434290826659207222585733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 206: 7^2 divides 97 + 1 (5^206+1 -> 720016715917900826434290826659207222585733 -> 97).
theorem ke206 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 206 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g720016715917900826434290826659207222585733 : 720016715917900826434290826659207222585733 ∈ P := S7 720016715917900826434290826659207222585733 prime_720016715917900826434290826659207222585733 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 720016715917900826434290826659207222585733 ∣ 1 + 5 ^ 206).trans hd)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 720016715917900826434290826659207222585733 g720016715917900826434290826659207222585733 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)

theorem prime_22144561409 : Nat.Prime 22144561409 := by
  refine lucas_primality 22144561409 (3 : ZMod 22144561409) ?_ (fun q hq hd => ?_)
  · rw [show 22144561409 - 1 = 22144561408 from by norm_num]
    reduce_mod_char
  · have e : 22144561409 - 1 = [2 ^ 8, 19 ^ 1, 211 ^ 1, 21577 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22144561409 - 1) / 2 = 11072280704 from by norm_num]
      have h2 : (3 : ZMod 22144561409) ^ 11072280704 = ((22144561408 : ℕ) : ZMod 22144561409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22144561409 - 1) / 19 = 1165503232 from by norm_num]
      have h2 : (3 : ZMod 22144561409) ^ 1165503232 = ((12755554986 : ℕ) : ZMod 22144561409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22144561409 - 1) / 211 = 104950528 from by norm_num]
      have h2 : (3 : ZMod 22144561409) ^ 104950528 = ((4334247098 : ℕ) : ZMod 22144561409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22144561409 - 1) / 21577 = 1026304 from by norm_num]
      have h2 : (3 : ZMod 22144561409) ^ 1026304 = ((2026924051 : ℕ) : ZMod 22144561409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 211: 3 divides 5^211 + 1 and 22144561409 + 1 (5^211+1 -> 22144561409).
theorem ke211 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 211 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g22144561409 : 22144561409 ∈ P := S7 22144561409 prime_22144561409 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 22144561409 ∣ 1 + 5 ^ 211).trans hd)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 211).trans hd) 22144561409 g22144561409 (by norm_num)

-- e an odd multiple of 212: 3^2 divides 24452081 + 1 (5^212+1 -> 24452081).
theorem ke212 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 212 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g24452081 : 24452081 ∈ P := S7 24452081 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 24452081 ∣ 1 + 5 ^ 212).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 24452081 g24452081 (by norm_num)

-- e an odd multiple of 214: 3^2 divides 25253 + 1 (5^214+1 -> 25253).
theorem ke214 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 214 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g25253 : 25253 ∈ P := S7 25253 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 25253 ∣ 1 + 5 ^ 214).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 25253 g25253 (by norm_num)

theorem prime_938804357 : Nat.Prime 938804357 := by
  refine lucas_primality 938804357 (2 : ZMod 938804357) ?_ (fun q hq hd => ?_)
  · rw [show 938804357 - 1 = 938804356 from by norm_num]
    reduce_mod_char
  · have e : 938804357 - 1 = [2 ^ 2, 7 ^ 1, 29 ^ 1, 109 ^ 1, 10607 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (938804357 - 1) / 2 = 469402178 from by norm_num]
      have h2 : (2 : ZMod 938804357) ^ 469402178 = ((938804356 : ℕ) : ZMod 938804357) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (938804357 - 1) / 7 = 134114908 from by norm_num]
      have h2 : (2 : ZMod 938804357) ^ 134114908 = ((450741968 : ℕ) : ZMod 938804357) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (938804357 - 1) / 29 = 32372564 from by norm_num]
      have h2 : (2 : ZMod 938804357) ^ 32372564 = ((568549908 : ℕ) : ZMod 938804357) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (938804357 - 1) / 109 = 8612884 from by norm_num]
      have h2 : (2 : ZMod 938804357) ^ 8612884 = ((686698254 : ℕ) : ZMod 938804357) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (938804357 - 1) / 10607 = 88508 from by norm_num]
      have h2 : (2 : ZMod 938804357) ^ 88508 = ((590895084 : ℕ) : ZMod 938804357) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 218: 3 divides 938804357 + 1 and 401 + 1 (5^218+1 -> 938804357; 5^218+1 -> 938804357 -> 401).
theorem ke218 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 218 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g938804357 : 938804357 ∈ P := S7 938804357 prime_938804357 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 938804357 ∣ 1 + 5 ^ 218).trans hd)
  have g401 : 401 ∈ P := S1 401 (by norm_num) (by norm_num) (hnz (by norm_num)) 938804357 g938804357 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 938804357 g938804357 401 g401 (by norm_num) (by norm_num)) (by norm_num)

theorem prime_187373521 : Nat.Prime 187373521 := by
  refine lucas_primality 187373521 (7 : ZMod 187373521) ?_ (fun q hq hd => ?_)
  · rw [show 187373521 - 1 = 187373520 from by norm_num]
    reduce_mod_char
  · have e : 187373521 - 1 = [2 ^ 4, 3 ^ 3, 5 ^ 1, 223 ^ 1, 389 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187373521 - 1) / 2 = 93686760 from by norm_num]
      have h2 : (7 : ZMod 187373521) ^ 93686760 = ((187373520 : ℕ) : ZMod 187373521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187373521 - 1) / 3 = 62457840 from by norm_num]
      have h2 : (7 : ZMod 187373521) ^ 62457840 = ((21536500 : ℕ) : ZMod 187373521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187373521 - 1) / 5 = 37474704 from by norm_num]
      have h2 : (7 : ZMod 187373521) ^ 37474704 = ((13538965 : ℕ) : ZMod 187373521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187373521 - 1) / 223 = 840240 from by norm_num]
      have h2 : (7 : ZMod 187373521) ^ 840240 = ((151198221 : ℕ) : ZMod 187373521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (187373521 - 1) / 389 = 481680 from by norm_num]
      have h2 : (7 : ZMod 187373521) ^ 481680 = ((62793665 : ℕ) : ZMod 187373521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 223: 3^2 divides 503 + 1 (5^223+1 -> 187373521 -> 13383823 -> 503).
theorem ke223 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 223 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g187373521 : 187373521 ∈ P := S7 187373521 prime_187373521 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 187373521 ∣ 1 + 5 ^ 223).trans hd)
  have g13383823 : 13383823 ∈ P := S1 13383823 (by norm_num) (by norm_num) (hnz (by norm_num)) 187373521 g187373521 (by norm_num)
  have g503 : 503 ∈ P := S1 503 (by norm_num) (by norm_num) (hnz (by norm_num)) 13383823 g13383823 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 503 g503 (by norm_num)

theorem prime_5279424251983491133 : Nat.Prime 5279424251983491133 := by
  refine lucas_primality 5279424251983491133 (5 : ZMod 5279424251983491133) ?_ (fun q hq hd => ?_)
  · rw [show 5279424251983491133 - 1 = 5279424251983491132 from by norm_num]
    reduce_mod_char
  · have e : 5279424251983491133 - 1 = [2 ^ 2, 3 ^ 5, 41 ^ 1, 61 ^ 1, 863 ^ 1, 7789 ^ 1, 323083 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5279424251983491133 - 1) / 2 = 2639712125991745566 from by norm_num]
      have h2 : (5 : ZMod 5279424251983491133) ^ 2639712125991745566 = ((5279424251983491132 : ℕ) : ZMod 5279424251983491133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5279424251983491133 - 1) / 3 = 1759808083994497044 from by norm_num]
      have h2 : (5 : ZMod 5279424251983491133) ^ 1759808083994497044 = ((4583241373260617763 : ℕ) : ZMod 5279424251983491133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5279424251983491133 - 1) / 41 = 128766445170329052 from by norm_num]
      have h2 : (5 : ZMod 5279424251983491133) ^ 128766445170329052 = ((3987163924603440440 : ℕ) : ZMod 5279424251983491133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5279424251983491133 - 1) / 61 = 86547938557106412 from by norm_num]
      have h2 : (5 : ZMod 5279424251983491133) ^ 86547938557106412 = ((3677292032125373449 : ℕ) : ZMod 5279424251983491133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5279424251983491133 - 1) / 863 = 6117525205079364 from by norm_num]
      have h2 : (5 : ZMod 5279424251983491133) ^ 6117525205079364 = ((1941570617322985144 : ℕ) : ZMod 5279424251983491133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5279424251983491133 - 1) / 7789 = 677805142121388 from by norm_num]
      have h2 : (5 : ZMod 5279424251983491133) ^ 677805142121388 = ((4730603304811436657 : ℕ) : ZMod 5279424251983491133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5279424251983491133 - 1) / 323083 = 16340767703604 from by norm_num]
      have h2 : (5 : ZMod 5279424251983491133) ^ 16340767703604 = ((4501265398081538201 : ℕ) : ZMod 5279424251983491133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_16395906853201250737837672789 : Nat.Prime 16395906853201250737837672789 := by
  refine lucas_primality 16395906853201250737837672789 (6 : ZMod 16395906853201250737837672789) ?_ (fun q hq hd => ?_)
  · rw [show 16395906853201250737837672789 - 1 = 16395906853201250737837672788 from by norm_num]
    reduce_mod_char
  · have e : 16395906853201250737837672789 - 1 = [2 ^ 2, 3 ^ 1, 23 ^ 1, 29 ^ 1, 388009 ^ 1, 5279424251983491133 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16395906853201250737837672789 - 1) / 2 = 8197953426600625368918836394 from by norm_num]
      have h2 : (6 : ZMod 16395906853201250737837672789) ^ 8197953426600625368918836394 = ((16395906853201250737837672788 : ℕ) : ZMod 16395906853201250737837672789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16395906853201250737837672789 - 1) / 3 = 5465302284400416912612557596 from by norm_num]
      have h2 : (6 : ZMod 16395906853201250737837672789) ^ 5465302284400416912612557596 = ((12315726722095531530800331124 : ℕ) : ZMod 16395906853201250737837672789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16395906853201250737837672789 - 1) / 23 = 712865515356576119036420556 from by norm_num]
      have h2 : (6 : ZMod 16395906853201250737837672789) ^ 712865515356576119036420556 = ((12957231439452111678719118769 : ℕ) : ZMod 16395906853201250737837672789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16395906853201250737837672789 - 1) / 29 = 565376098386250025442678372 from by norm_num]
      have h2 : (6 : ZMod 16395906853201250737837672789) ^ 565376098386250025442678372 = ((7423700510653719226889574692 : ℕ) : ZMod 16395906853201250737837672789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16395906853201250737837672789 - 1) / 388009 = 42256511712875863028532 from by norm_num]
      have h2 : (6 : ZMod 16395906853201250737837672789) ^ 42256511712875863028532 = ((6417228058135357698529321439 : ℕ) : ZMod 16395906853201250737837672789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_5279424251983491133).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16395906853201250737837672789 - 1) / 5279424251983491133 = 3105624036 from by norm_num]
      have h2 : (6 : ZMod 16395906853201250737837672789) ^ 3105624036 = ((5988584130027148257011253639 : ℕ) : ZMod 16395906853201250737837672789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_234597923865761 : Nat.Prime 234597923865761 := by
  refine lucas_primality 234597923865761 (3 : ZMod 234597923865761) ?_ (fun q hq hd => ?_)
  · rw [show 234597923865761 - 1 = 234597923865760 from by norm_num]
    reduce_mod_char
  · have e : 234597923865761 - 1 = [2 ^ 5, 5 ^ 1, 7 ^ 1, 13 ^ 1, 37057 ^ 1, 434803 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234597923865761 - 1) / 2 = 117298961932880 from by norm_num]
      have h2 : (3 : ZMod 234597923865761) ^ 117298961932880 = ((234597923865760 : ℕ) : ZMod 234597923865761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234597923865761 - 1) / 5 = 46919584773152 from by norm_num]
      have h2 : (3 : ZMod 234597923865761) ^ 46919584773152 = ((219940123913298 : ℕ) : ZMod 234597923865761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234597923865761 - 1) / 7 = 33513989123680 from by norm_num]
      have h2 : (3 : ZMod 234597923865761) ^ 33513989123680 = ((225858593107102 : ℕ) : ZMod 234597923865761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234597923865761 - 1) / 13 = 18045994143520 from by norm_num]
      have h2 : (3 : ZMod 234597923865761) ^ 18045994143520 = ((207529409057557 : ℕ) : ZMod 234597923865761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234597923865761 - 1) / 37057 = 6330731680 from by norm_num]
      have h2 : (3 : ZMod 234597923865761) ^ 6330731680 = ((151588837666625 : ℕ) : ZMod 234597923865761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234597923865761 - 1) / 434803 = 539549920 from by norm_num]
      have h2 : (3 : ZMod 234597923865761) ^ 539549920 = ((108334189697492 : ℕ) : ZMod 234597923865761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11913287466894338293503913814067039110653443245880449 : Nat.Prime 11913287466894338293503913814067039110653443245880449 := by
  refine lucas_primality 11913287466894338293503913814067039110653443245880449 (3 : ZMod 11913287466894338293503913814067039110653443245880449) ?_ (fun q hq hd => ?_)
  · rw [show 11913287466894338293503913814067039110653443245880449 - 1 = 11913287466894338293503913814067039110653443245880448 from by norm_num]
    reduce_mod_char
  · have e : 11913287466894338293503913814067039110653443245880449 - 1 = [2 ^ 7, 113 ^ 1, 214133 ^ 1, 234597923865761 ^ 1, 16395906853201250737837672789 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11913287466894338293503913814067039110653443245880449 - 1) / 2 = 5956643733447169146751956907033519555326721622940224 from by norm_num]
      have h2 : (3 : ZMod 11913287466894338293503913814067039110653443245880449) ^ 5956643733447169146751956907033519555326721622940224 = ((11913287466894338293503913814067039110653443245880448 : ℕ) : ZMod 11913287466894338293503913814067039110653443245880449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11913287466894338293503913814067039110653443245880449 - 1) / 113 = 105427322715879099942512511628911850536756134919296 from by norm_num]
      have h2 : (3 : ZMod 11913287466894338293503913814067039110653443245880449) ^ 105427322715879099942512511628911850536756134919296 = ((5126104228164356393905985496093662681155914593964715 : ℕ) : ZMod 11913287466894338293503913814067039110653443245880449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11913287466894338293503913814067039110653443245880449 - 1) / 214133 = 55634990715556865562542503089514643285497533056 from by norm_num]
      have h2 : (3 : ZMod 11913287466894338293503913814067039110653443245880449) ^ 55634990715556865562542503089514643285497533056 = ((741298118775065751863494593354741220681253312722734 : ℕ) : ZMod 11913287466894338293503913814067039110653443245880449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_234597923865761).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11913287466894338293503913814067039110653443245880449 - 1) / 234597923865761 = 50781725901850804088285384418296816768 from by norm_num]
      have h2 : (3 : ZMod 11913287466894338293503913814067039110653443245880449) ^ 50781725901850804088285384418296816768 = ((11157215666594840286701724956805980327237135825488783 : ℕ) : ZMod 11913287466894338293503913814067039110653443245880449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_16395906853201250737837672789).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11913287466894338293503913814067039110653443245880449 - 1) / 16395906853201250737837672789 = 726601314191310211080832 from by norm_num]
      have h2 : (3 : ZMod 11913287466894338293503913814067039110653443245880449) ^ 726601314191310211080832 = ((9218876369484012676794354073065401658822386859412155 : ℕ) : ZMod 11913287466894338293503913814067039110653443245880449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_956554219 : Nat.Prime 956554219 := by
  refine lucas_primality 956554219 (2 : ZMod 956554219) ?_ (fun q hq hd => ?_)
  · rw [show 956554219 - 1 = 956554218 from by norm_num]
    reduce_mod_char
  · have e : 956554219 - 1 = [2 ^ 1, 3 ^ 3, 17713967 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (956554219 - 1) / 2 = 478277109 from by norm_num]
      have h2 : (2 : ZMod 956554219) ^ 478277109 = ((956554218 : ℕ) : ZMod 956554219) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (956554219 - 1) / 3 = 318851406 from by norm_num]
      have h2 : (2 : ZMod 956554219) ^ 318851406 = ((649958794 : ℕ) : ZMod 956554219) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (956554219 - 1) / 17713967 = 54 from by norm_num]
      have h2 : (2 : ZMod 956554219) ^ 54 = ((307513679 : ℕ) : ZMod 956554219) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_17177374041620327 : Nat.Prime 17177374041620327 := by
  refine lucas_primality 17177374041620327 (5 : ZMod 17177374041620327) ?_ (fun q hq hd => ?_)
  · rw [show 17177374041620327 - 1 = 17177374041620326 from by norm_num]
    reduce_mod_char
  · have e : 17177374041620327 - 1 = [2 ^ 1, 29 ^ 1, 409 ^ 1, 757 ^ 1, 956554219 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17177374041620327 - 1) / 2 = 8588687020810163 from by norm_num]
      have h2 : (5 : ZMod 17177374041620327) ^ 8588687020810163 = ((17177374041620326 : ℕ) : ZMod 17177374041620327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17177374041620327 - 1) / 29 = 592323242814494 from by norm_num]
      have h2 : (5 : ZMod 17177374041620327) ^ 592323242814494 = ((9684270042182553 : ℕ) : ZMod 17177374041620327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17177374041620327 - 1) / 409 = 41998469539414 from by norm_num]
      have h2 : (5 : ZMod 17177374041620327) ^ 41998469539414 = ((15827432327891449 : ℕ) : ZMod 17177374041620327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17177374041620327 - 1) / 757 = 22691379183118 from by norm_num]
      have h2 : (5 : ZMod 17177374041620327) ^ 22691379183118 = ((1693330925174100 : ℕ) : ZMod 17177374041620327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_956554219).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17177374041620327 - 1) / 956554219 = 17957554 from by norm_num]
      have h2 : (5 : ZMod 17177374041620327) ^ 17957554 = ((4914019735927434 : ℕ) : ZMod 17177374041620327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 226: 3^2 divides 17177374041620327 + 1 (5^226+1 -> 11913287466894338293503913814067039110653443245880449 -> 17177374041620327).
theorem ke226 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 226 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g11913287466894338293503913814067039110653443245880449 : 11913287466894338293503913814067039110653443245880449 ∈ P := S7 11913287466894338293503913814067039110653443245880449 prime_11913287466894338293503913814067039110653443245880449 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 11913287466894338293503913814067039110653443245880449 ∣ 1 + 5 ^ 226).trans hd)
  have g17177374041620327 : 17177374041620327 ∈ P := S1 17177374041620327 prime_17177374041620327 (by norm_num) (hnz (by norm_num)) 11913287466894338293503913814067039110653443245880449 g11913287466894338293503913814067039110653443245880449 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 17177374041620327 g17177374041620327 (by norm_num)

theorem prime_6281197643003 : Nat.Prime 6281197643003 := by
  refine lucas_primality 6281197643003 (2 : ZMod 6281197643003) ?_ (fun q hq hd => ?_)
  · rw [show 6281197643003 - 1 = 6281197643002 from by norm_num]
    reduce_mod_char
  · have e : 6281197643003 - 1 = [2 ^ 1, 223 ^ 1, 24593 ^ 1, 572659 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6281197643003 - 1) / 2 = 3140598821501 from by norm_num]
      have h2 : (2 : ZMod 6281197643003) ^ 3140598821501 = ((6281197643002 : ℕ) : ZMod 6281197643003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6281197643003 - 1) / 223 = 28166805574 from by norm_num]
      have h2 : (2 : ZMod 6281197643003) ^ 28166805574 = ((4782329382610 : ℕ) : ZMod 6281197643003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6281197643003 - 1) / 24593 = 255405914 from by norm_num]
      have h2 : (2 : ZMod 6281197643003) ^ 255405914 = ((5398358343365 : ℕ) : ZMod 6281197643003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6281197643003 - 1) / 572659 = 10968478 from by norm_num]
      have h2 : (2 : ZMod 6281197643003) ^ 10968478 = ((5017497439746 : ℕ) : ZMod 6281197643003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2864226125209369 : Nat.Prime 2864226125209369 := by
  refine lucas_primality 2864226125209369 (11 : ZMod 2864226125209369) ?_ (fun q hq hd => ?_)
  · rw [show 2864226125209369 - 1 = 2864226125209368 from by norm_num]
    reduce_mod_char
  · have e : 2864226125209369 - 1 = [2 ^ 3, 3 ^ 1, 19 ^ 1, 6281197643003 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2864226125209369 - 1) / 2 = 1432113062604684 from by norm_num]
      have h2 : (11 : ZMod 2864226125209369) ^ 1432113062604684 = ((2864226125209368 : ℕ) : ZMod 2864226125209369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2864226125209369 - 1) / 3 = 954742041736456 from by norm_num]
      have h2 : (11 : ZMod 2864226125209369) ^ 954742041736456 = ((1859169860156508 : ℕ) : ZMod 2864226125209369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2864226125209369 - 1) / 19 = 150748743432072 from by norm_num]
      have h2 : (11 : ZMod 2864226125209369) ^ 150748743432072 = ((458276180033499 : ℕ) : ZMod 2864226125209369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6281197643003).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2864226125209369 - 1) / 6281197643003 = 456 from by norm_num]
      have h2 : (11 : ZMod 2864226125209369) ^ 456 = ((801420605368186 : ℕ) : ZMod 2864226125209369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2108505761893 : Nat.Prime 2108505761893 := by
  refine lucas_primality 2108505761893 (2 : ZMod 2108505761893) ?_ (fun q hq hd => ?_)
  · rw [show 2108505761893 - 1 = 2108505761892 from by norm_num]
    reduce_mod_char
  · have e : 2108505761893 - 1 = [2 ^ 2, 3 ^ 8, 19 ^ 1, 71 ^ 1, 59557 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2108505761893 - 1) / 2 = 1054252880946 from by norm_num]
      have h2 : (2 : ZMod 2108505761893) ^ 1054252880946 = ((2108505761892 : ℕ) : ZMod 2108505761893) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2108505761893 - 1) / 3 = 702835253964 from by norm_num]
      have h2 : (2 : ZMod 2108505761893) ^ 702835253964 = ((606754641710 : ℕ) : ZMod 2108505761893) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2108505761893 - 1) / 19 = 110973987468 from by norm_num]
      have h2 : (2 : ZMod 2108505761893) ^ 110973987468 = ((2108505746268 : ℕ) : ZMod 2108505761893) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2108505761893 - 1) / 71 = 29697264252 from by norm_num]
      have h2 : (2 : ZMod 2108505761893) ^ 29697264252 = ((148931878204 : ℕ) : ZMod 2108505761893) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2108505761893 - 1) / 59557 = 35403156 from by norm_num]
      have h2 : (2 : ZMod 2108505761893) ^ 35403156 = ((207523550733 : ℕ) : ZMod 2108505761893) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_53590717 : Nat.Prime 53590717 := by
  refine lucas_primality 53590717 (6 : ZMod 53590717) ?_ (fun q hq hd => ?_)
  · rw [show 53590717 - 1 = 53590716 from by norm_num]
    reduce_mod_char
  · have e : 53590717 - 1 = [2 ^ 2, 3 ^ 2, 19 ^ 1, 47 ^ 1, 1667 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53590717 - 1) / 2 = 26795358 from by norm_num]
      have h2 : (6 : ZMod 53590717) ^ 26795358 = ((53590716 : ℕ) : ZMod 53590717) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53590717 - 1) / 3 = 17863572 from by norm_num]
      have h2 : (6 : ZMod 53590717) ^ 17863572 = ((32051285 : ℕ) : ZMod 53590717) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53590717 - 1) / 19 = 2820564 from by norm_num]
      have h2 : (6 : ZMod 53590717) ^ 2820564 = ((14329729 : ℕ) : ZMod 53590717) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53590717 - 1) / 47 = 1140228 from by norm_num]
      have h2 : (6 : ZMod 53590717) ^ 1140228 = ((40801479 : ℕ) : ZMod 53590717) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53590717 - 1) / 1667 = 32148 from by norm_num]
      have h2 : (6 : ZMod 53590717) ^ 32148 = ((28279511 : ℕ) : ZMod 53590717) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_923108138011 : Nat.Prime 923108138011 := by
  refine lucas_primality 923108138011 (3 : ZMod 923108138011) ?_ (fun q hq hd => ?_)
  · rw [show 923108138011 - 1 = 923108138010 from by norm_num]
    reduce_mod_char
  · have e : 923108138011 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 1, 367 ^ 1, 1153 ^ 1, 24239 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (923108138011 - 1) / 2 = 461554069005 from by norm_num]
      have h2 : (3 : ZMod 923108138011) ^ 461554069005 = ((923108138010 : ℕ) : ZMod 923108138011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (923108138011 - 1) / 3 = 307702712670 from by norm_num]
      have h2 : (3 : ZMod 923108138011) ^ 307702712670 = ((306332178943 : ℕ) : ZMod 923108138011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (923108138011 - 1) / 5 = 184621627602 from by norm_num]
      have h2 : (3 : ZMod 923108138011) ^ 184621627602 = ((599568005050 : ℕ) : ZMod 923108138011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (923108138011 - 1) / 367 = 2515281030 from by norm_num]
      have h2 : (3 : ZMod 923108138011) ^ 2515281030 = ((295289814267 : ℕ) : ZMod 923108138011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (923108138011 - 1) / 1153 = 800614170 from by norm_num]
      have h2 : (3 : ZMod 923108138011) ^ 800614170 = ((498388445752 : ℕ) : ZMod 923108138011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (923108138011 - 1) / 24239 = 38083590 from by norm_num]
      have h2 : (3 : ZMod 923108138011) ^ 38083590 = ((123016110887 : ℕ) : ZMod 923108138011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_75649382555448580095589 : Nat.Prime 75649382555448580095589 := by
  refine lucas_primality 75649382555448580095589 (6 : ZMod 75649382555448580095589) ?_ (fun q hq hd => ?_)
  · rw [show 75649382555448580095589 - 1 = 75649382555448580095588 from by norm_num]
    reduce_mod_char
  · have e : 75649382555448580095589 - 1 = [2 ^ 2, 3 ^ 1, 7 ^ 1, 19 ^ 1, 139 ^ 1, 369407 ^ 1, 923108138011 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75649382555448580095589 - 1) / 2 = 37824691277724290047794 from by norm_num]
      have h2 : (6 : ZMod 75649382555448580095589) ^ 37824691277724290047794 = ((75649382555448580095588 : ℕ) : ZMod 75649382555448580095589) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75649382555448580095589 - 1) / 3 = 25216460851816193365196 from by norm_num]
      have h2 : (6 : ZMod 75649382555448580095589) ^ 25216460851816193365196 = ((75649382536375093767464 : ℕ) : ZMod 75649382555448580095589) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75649382555448580095589 - 1) / 7 = 10807054650778368585084 from by norm_num]
      have h2 : (6 : ZMod 75649382555448580095589) ^ 10807054650778368585084 = ((50753349019092197876519 : ℕ) : ZMod 75649382555448580095589) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75649382555448580095589 - 1) / 19 = 3981546450286767373452 from by norm_num]
      have h2 : (6 : ZMod 75649382555448580095589) ^ 3981546450286767373452 = ((75649382460081148454969 : ℕ) : ZMod 75649382555448580095589) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75649382555448580095589 - 1) / 139 = 544240162269414245292 from by norm_num]
      have h2 : (6 : ZMod 75649382555448580095589) ^ 544240162269414245292 = ((17018315915900300296993 : ℕ) : ZMod 75649382555448580095589) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75649382555448580095589 - 1) / 369407 = 204786001768912284 from by norm_num]
      have h2 : (6 : ZMod 75649382555448580095589) ^ 204786001768912284 = ((39970806132106205103754 : ℕ) : ZMod 75649382555448580095589) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_923108138011).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75649382555448580095589 - 1) / 923108138011 = 81950726508 from by norm_num]
      have h2 : (6 : ZMod 75649382555448580095589) ^ 81950726508 = ((32384212650734896870905 : ℕ) : ZMod 75649382555448580095589) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4162889439151 : Nat.Prime 4162889439151 := by
  refine lucas_primality 4162889439151 (3 : ZMod 4162889439151) ?_ (fun q hq hd => ?_)
  · rw [show 4162889439151 - 1 = 4162889439150 from by norm_num]
    reduce_mod_char
  · have e : 4162889439151 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 2, 13 ^ 1, 113 ^ 1, 18892169 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4162889439151 - 1) / 2 = 2081444719575 from by norm_num]
      have h2 : (3 : ZMod 4162889439151) ^ 2081444719575 = ((4162889439150 : ℕ) : ZMod 4162889439151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4162889439151 - 1) / 3 = 1387629813050 from by norm_num]
      have h2 : (3 : ZMod 4162889439151) ^ 1387629813050 = ((3174075221816 : ℕ) : ZMod 4162889439151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4162889439151 - 1) / 5 = 832577887830 from by norm_num]
      have h2 : (3 : ZMod 4162889439151) ^ 832577887830 = ((3421889847648 : ℕ) : ZMod 4162889439151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4162889439151 - 1) / 13 = 320222264550 from by norm_num]
      have h2 : (3 : ZMod 4162889439151) ^ 320222264550 = ((1969202975491 : ℕ) : ZMod 4162889439151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4162889439151 - 1) / 113 = 36839729550 from by norm_num]
      have h2 : (3 : ZMod 4162889439151) ^ 36839729550 = ((2825396935920 : ℕ) : ZMod 4162889439151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4162889439151 - 1) / 18892169 = 220350 from by norm_num]
      have h2 : (3 : ZMod 4162889439151) ^ 220350 = ((1580948042380 : ℕ) : ZMod 4162889439151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_446161838530447577 : Nat.Prime 446161838530447577 := by
  refine lucas_primality 446161838530447577 (3 : ZMod 446161838530447577) ?_ (fun q hq hd => ?_)
  · rw [show 446161838530447577 - 1 = 446161838530447576 from by norm_num]
    reduce_mod_char
  · have e : 446161838530447577 - 1 = [2 ^ 3, 13397 ^ 1, 4162889439151 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (446161838530447577 - 1) / 2 = 223080919265223788 from by norm_num]
      have h2 : (3 : ZMod 446161838530447577) ^ 223080919265223788 = ((446161838530447576 : ℕ) : ZMod 446161838530447577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (446161838530447577 - 1) / 13397 = 33303115513208 from by norm_num]
      have h2 : (3 : ZMod 446161838530447577) ^ 33303115513208 = ((161757869925794068 : ℕ) : ZMod 446161838530447577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4162889439151).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (446161838530447577 - 1) / 4162889439151 = 107176 from by norm_num]
      have h2 : (3 : ZMod 446161838530447577) ^ 107176 = ((262494542170348443 : ℕ) : ZMod 446161838530447577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_86336058161143199543775877 : Nat.Prime 86336058161143199543775877 := by
  refine lucas_primality 86336058161143199543775877 (6 : ZMod 86336058161143199543775877) ?_ (fun q hq hd => ?_)
  · rw [show 86336058161143199543775877 - 1 = 86336058161143199543775876 from by norm_num]
    reduce_mod_char
  · have e : 86336058161143199543775877 - 1 = [2 ^ 2, 3 ^ 2, 19 ^ 1, 282907 ^ 1, 446161838530447577 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86336058161143199543775877 - 1) / 2 = 43168029080571599771887938 from by norm_num]
      have h2 : (6 : ZMod 86336058161143199543775877) ^ 43168029080571599771887938 = ((86336058161143199543775876 : ℕ) : ZMod 86336058161143199543775877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86336058161143199543775877 - 1) / 3 = 28778686053714399847925292 from by norm_num]
      have h2 : (6 : ZMod 86336058161143199543775877) ^ 28778686053714399847925292 = ((18453648064598496990912116 : ℕ) : ZMod 86336058161143199543775877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86336058161143199543775877 - 1) / 19 = 4544003061112799975988204 from by norm_num]
      have h2 : (6 : ZMod 86336058161143199543775877) ^ 4544003061112799975988204 = ((73302291450656656094455909 : ℕ) : ZMod 86336058161143199543775877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86336058161143199543775877 - 1) / 282907 = 305174697554826142668 from by norm_num]
      have h2 : (6 : ZMod 86336058161143199543775877) ^ 305174697554826142668 = ((78204540668558505838100683 : ℕ) : ZMod 86336058161143199543775877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_446161838530447577).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86336058161143199543775877 - 1) / 446161838530447577 = 193508388 from by norm_num]
      have h2 : (6 : ZMod 86336058161143199543775877) ^ 193508388 = ((15832353335353488943678759 : ℕ) : ZMod 86336058161143199543775877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11735415506748076408140121 : Nat.Prime 11735415506748076408140121 := by
  refine lucas_primality 11735415506748076408140121 (34 : ZMod 11735415506748076408140121) ?_ (fun q hq hd => ?_)
  · rw [show 11735415506748076408140121 - 1 = 11735415506748076408140120 from by norm_num]
    reduce_mod_char
  · have e : 11735415506748076408140121 - 1 = [2 ^ 3, 3 ^ 3, 5 ^ 1, 7 ^ 1, 19 ^ 1, 829 ^ 1, 1489 ^ 1, 5167 ^ 1, 50993 ^ 1, 251203 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11735415506748076408140121 - 1) / 2 = 5867707753374038204070060 from by norm_num]
      have h2 : (34 : ZMod 11735415506748076408140121) ^ 5867707753374038204070060 = ((11735415506748076408140120 : ℕ) : ZMod 11735415506748076408140121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11735415506748076408140121 - 1) / 3 = 3911805168916025469380040 from by norm_num]
      have h2 : (34 : ZMod 11735415506748076408140121) ^ 3911805168916025469380040 = ((11735415506729002921811995 : ℕ) : ZMod 11735415506748076408140121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11735415506748076408140121 - 1) / 5 = 2347083101349615281628024 from by norm_num]
      have h2 : (34 : ZMod 11735415506748076408140121) ^ 2347083101349615281628024 = ((8929741216246147724428196 : ℕ) : ZMod 11735415506748076408140121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11735415506748076408140121 - 1) / 7 = 1676487929535439486877160 from by norm_num]
      have h2 : (34 : ZMod 11735415506748076408140121) ^ 1676487929535439486877160 = ((996951613021366075051697 : ℕ) : ZMod 11735415506748076408140121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11735415506748076408140121 - 1) / 19 = 617653447723582968849480 from by norm_num]
      have h2 : (34 : ZMod 11735415506748076408140121) ^ 617653447723582968849480 = ((59604644775390625 : ℕ) : ZMod 11735415506748076408140121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11735415506748076408140121 - 1) / 829 = 14156110382084531252280 from by norm_num]
      have h2 : (34 : ZMod 11735415506748076408140121) ^ 14156110382084531252280 = ((11082625732975534506255770 : ℕ) : ZMod 11735415506748076408140121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11735415506748076408140121 - 1) / 1489 = 7881407324881179589080 from by norm_num]
      have h2 : (34 : ZMod 11735415506748076408140121) ^ 7881407324881179589080 = ((10541995976017991147028453 : ℕ) : ZMod 11735415506748076408140121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11735415506748076408140121 - 1) / 5167 = 2271224212647198840360 from by norm_num]
      have h2 : (34 : ZMod 11735415506748076408140121) ^ 2271224212647198840360 = ((3279272854191957474946677 : ℕ) : ZMod 11735415506748076408140121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11735415506748076408140121 - 1) / 50993 = 230137773944425242840 from by norm_num]
      have h2 : (34 : ZMod 11735415506748076408140121) ^ 230137773944425242840 = ((6866512777377120251700087 : ℕ) : ZMod 11735415506748076408140121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11735415506748076408140121 - 1) / 251203 = 46716860494293764040 from by norm_num]
      have h2 : (34 : ZMod 11735415506748076408140121) ^ 46716860494293764040 = ((6333979593882897822133687 : ℕ) : ZMod 11735415506748076408140121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 : Nat.Prime 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 := by
  refine lucas_primality 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ?_ (fun q hq hd => ?_)
  · rw [show 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1 = 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200520 from by norm_num]
    reduce_mod_char
  · have e : 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 7 ^ 1, 13 ^ 1, 31 ^ 1, 191 ^ 1, 229 ^ 1, 601 ^ 1, 761 ^ 1, 6271 ^ 1, 19609 ^ 1, 22573 ^ 1, 213029 ^ 1, 3981071 ^ 1, 53590717 ^ 1, 4885168129 ^ 1, 2108505761893 ^ 1, 2864226125209369 ^ 1, 75649382555448580095589 ^ 1, 11735415506748076408140121 ^ 1, 86336058161143199543775877 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 2 = 965939101741515985867639391028031123272803327801508073555478921593120140649903478905550021542502197275088260191666968496627491506482480569199348489443461100260 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 965939101741515985867639391028031123272803327801508073555478921593120140649903478905550021542502197275088260191666968496627491506482480569199348489443461100260 = ((1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200520 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 3 = 643959401161010657245092927352020748848535551867672049036985947728746760433268985937033347695001464850058840127777978997751661004321653712799565659628974066840 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 643959401161010657245092927352020748848535551867672049036985947728746760433268985937033347695001464850058840127777978997751661004321653712799565659628974066840 = ((214733870528386509138818402680024636738250617750584813924415981729334102509740282553905874855638850361292010448230881474162171704522394742806675381460408355093 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 5 = 386375640696606394347055756411212449309121331120603229422191568637248056259961391562220008617000878910035304076666787398650996602592992227679739395777384440104 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 386375640696606394347055756411212449309121331120603229422191568637248056259961391562220008617000878910035304076666787398650996602592992227679739395777384440104 = ((607089444146617056599434112962009599311390488748841313974110728288436755189426091666526136123340588935311429615771574352956830609071037733204949687608461108283 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 7 = 275982600497575995962182683150866035220800950800430878158708263312320040185686708258728577583572056364310931483333419570464997573280708734056956711269560314360 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 275982600497575995962182683150866035220800950800430878158708263312320040185686708258728577583572056364310931483333419570464997573280708734056956711269560314360 = ((159018979590623355824160911144227806007819032101600984062694476827784952888521561895874528605729021929284776262425401175759779507455692778032042603406595240290 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 13 = 148606015652540920902713752465850942041969742738693549777765987937403098561523612139315387929615722657705886183333379768711921770228073933722976690683609400040 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 148606015652540920902713752465850942041969742738693549777765987937403098561523612139315387929615722657705886183333379768711921770228073933722976690683609400040 = ((107201234513526994894812470112517879882610833492373212797299835284437176324080839947532716894555667907634288768441524061033444159493435366136151303971209673351 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 31 = 62318651725259095862428347808260072469213117922677940229385736876975492945155063155196775583387238533876661947849481838492096226224676165754796676738287812920 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 62318651725259095862428347808260072469213117922677940229385736876975492945155063155196775583387238533876661947849481838492096226224676165754796676738287812920 = ((1022116302693834420655562331042176603430135854130968824520910240173079955213676351348095273067972891195410798465507052267403174387839009800065089708240713999126 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 191 = 10114545567973989380812977916523886107568621233523644749272030592598116656019931716288481900968609395550662410383947314100811429387251105436642392559617393720 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 10114545567973989380812977916523886107568621233523644749272030592598116656019931716288481900968609395550662410383947314100811429387251105436642392559617393720 = ((1925509535180174140173607189990415889777861826459056084863839708415877650230177173266762036144970345231981383026442325747616681056628815602236669183799725458553 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 229 = 8436149360187912540328728305921669198889112033200943873846977481162621315719681038476419402117923120306447687263466973769672414903777122875103480257148131880 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 8436149360187912540328728305921669198889112033200943873846977481162621315719681038476419402117923120306447687263466973769672414903777122875103480257148131880 = ((700649232162408535461864791644958065640130970938257885878534141944895541342930300743319094181060791015625 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 601 = 3214439606460951700058700136532549495084204085861923705675470620942163529616983290867054980174716130699128985662785252900590653931722065122127615605469088520 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 3214439606460951700058700136532549495084204085861923705675470620942163529616983290867054980174716130699128985662785252900590653931722065122127615605469088520 = ((1883104267193823187512495934246927506876431990456713146898333862697101044174666677720158099205912370939874360811601455586344170094968334481795354124812510928146 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 761 = 2538604735194522958916266467879188234619719652566381270842257349784809830880166830237976403528258074310350223893999917205328492789704285332981204965685837320 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 2538604735194522958916266467879188234619719652566381270842257349784809830880166830237976403528258074310350223893999917205328492789704285332981204965685837320 = ((1716419135165971248612779196235593470714255904041754394957159269013531545439954888765831842103342583306943129153404384612063010089165783847011400169716458903960 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 6271 = 308065412770376649933866812638504584044906180131241611722366104797678246101069519663705954885186476566763916501887089298876572000153876756242815656017688120 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 308065412770376649933866812638504584044906180131241611722366104797678246101069519663705954885186476566763916501887089298876572000153876756242815656017688120 = ((984632055779621118008829221660707743269446948545023084697013128536424320545235443018839445722839653326117788184071807574769301853290631341236516252618597304083 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 19609 = 98519975699068385523753316439189262407343906145291251318831038971198953608027281238773014589474445129796344555221272731564841807994541340119266509199190280 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 98519975699068385523753316439189262407343906145291251318831038971198953608027281238773014589474445129796344555221272731564841807994541340119266509199190280 = ((1072979834948993129211843646418326800862990786041202208017881465725664272881366213774040981603847729786847236164119919612189765724569342648220904478809938940110 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 22573 = 85583582309973506921334283527048343000292679555354456523765465077138186386382268985562399463297053761138374180806004385471801843484027871279789880781771240 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 85583582309973506921334283527048343000292679555354456523765465077138186386382268985562399463297053761138374180806004385471801843484027871279789880781771240 = ((1269259528442176817472452007878941426690078367528720255650903462351586000371711018137964740202008010366934914750781510702628825972118424370190810911754642774808 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 213029 = 9068616026376840579147809838360327685646586406559746077346078905624305992610428429045341446868756810341204814289763069785123072506395660395526885911715880 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 9068616026376840579147809838360327685646586406559746077346078905624305992610428429045341446868756810341204814289763069785123072506395660395526885911715880 = ((835604260271782134381043543810476887833781022178675323608282444846162529978190032443992767138056354527187061413360788116322043971877134451353292394818410023753 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 3981071 = 485265950665796207034558987281578812974098340773881236258021482959294190256794455012507951524854591779492634113617651379052265838254319287045796716232120 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 485265950665796207034558987281578812974098340773881236258021482959294190256794455012507951524854591779492634113617651379052265838254319287045796716232120 = ((932885367145765827211065867334335779618086473928668004648128049468585881902332136387559993605639132791000109046192426521145626932845772777932550832099160966369 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_53590717).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 53590717 = 36048747089594490249781110076509374684156710491539349009100920280395581968045080602506214706644145002765619284088584539618213785289809821697267028147560 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 36048747089594490249781110076509374684156710491539349009100920280395581968045080602506214706644145002765619284088584539618213785289809821697267028147560 = ((1336944000906308730297077521236101478321117557279821932683281144929773640720532073757167283097325437206630528816826538377392807190659245821304358123139479873153 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4885168129).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 4885168129 = 395457874216191991318724740262887735413211743649082532346750648177382367692878018817333531958159631756284333276287518536141457540603913396733514343880 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 395457874216191991318724740262887735413211743649082532346750648177382367692878018817333531958159631756284333276287518536141457540603913396733514343880 = ((1421295144591346081526419457880305820122666875313993439839418845053976570184835249673395651836269592145475069318262219358794356705194783455341304142780899098330 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2108505761893).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 2108505761893 = 916230933961786670075597334675033798345311456647546250799501154989865711774954394917617570798551829912249282335110170878969488581845619076214873640 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 916230933961786670075597334675033798345311456647546250799501154989865711774954394917617570798551829912249282335110170878969488581845619076214873640 = ((1710400050636840419663469216379541782180170861672335894541932038289151361143415546423631043275166652286691004503648879067112597550855649182249549170855974321914 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2864226125209369).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 2864226125209369 = 674485225338769533984096993562387062962929729794825648590697423362987638578194170653904676527369858526905804433794205275868686536947780303779080 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 674485225338769533984096993562387062962929729794825648590697423362987638578194170653904676527369858526905804433794205275868686536947780303779080 = ((168893543191679821592149806520253017106867894047609501897767070496035006782004401111237973878447207362718963606551569865371297517919544042644776483449217196763 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_75649382555448580095589).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 75649382555448580095589 = 25537263335454548888844914585472908768608239407682816437694142243321667286932060028664343740416632633216664771680370904428815841674800680 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 25537263335454548888844914585472908768608239407682816437694142243321667286932060028664343740416632633216664771680370904428815841674800680 = ((740671713041484838193668281876948787898227288844289548199160662227622119536060794122144273030721519197314850627738286634310165138453520531780741045510558920330 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_11735415506748076408140121).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 11735415506748076408140121 = 164619497483678104490274635054222891095429351546177746973532791411735552019969883181799633104664774367146643877883131305869420369466120 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 164619497483678104490274635054222891095429351546177746973532791411735552019969883181799633104664774367146643877883131305869420369466120 = ((154759222748558868791405538248241525243515628127312235344998617048314784757703761856712495028840420290481679101754556720764289348205867596054819930499137722950 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_86336058161143199543775877).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 - 1) / 86336058161143199543775877 = 22376261374792553303434326690055628804070635636028494224718431848408460517714211771035389620139787107154744197716938525964377614142760 from by norm_num]
      have h2 : (38 : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) ^ 22376261374792553303434326690055628804070635636028494224718431848408460517714211771035389620139787107154744197716938525964377614142760 = ((1587618042203683468704028628123246448503015784850865930789983667863604491589383209749248158719826191463932551820108974539305278022879769185529899500253395558039 : ℕ) : ZMod 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 229: 3 divides 5^229 + 1 and 29 + 1 (5^229+1 -> 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 -> 29).
theorem ke229 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 229 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 : 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 ∈ P := S7 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 prime_1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 ∣ 1 + 5 ^ 229).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 g1931878203483031971735278782056062246545606655603016147110957843186240281299806957811100043085004394550176520383333936993254983012964961138398696978886922200521 (by norm_num)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 229).trans hd) 29 g29 (by norm_num)

-- e an odd multiple of 236: 3^2 divides 1889 + 1 (5^236+1 -> 1889).
theorem ke236 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 236 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g1889 : 1889 ∈ P := S7 1889 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1889 ∣ 1 + 5 ^ 236).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1889 g1889 (by norm_num)

-- e an odd multiple of 241: 7 divides 181 + 1 and 13 + 1 (5^241+1 -> 1447 -> 181; 5^241+1 -> 1447 -> 181 -> 13).
theorem ke241 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 241 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g1447 : 1447 ∈ P := S7 1447 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1447 ∣ 1 + 5 ^ 241).trans hd)
  have g181 : 181 ∈ P := S1 181 (by norm_num) (by norm_num) (hnz (by norm_num)) 1447 g1447 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 13 g13 (by norm_num) (by norm_num)) (by norm_num)

theorem prime_1520427451429 : Nat.Prime 1520427451429 := by
  refine lucas_primality 1520427451429 (6 : ZMod 1520427451429) ?_ (fun q hq hd => ?_)
  · rw [show 1520427451429 - 1 = 1520427451428 from by norm_num]
    reduce_mod_char
  · have e : 1520427451429 - 1 = [2 ^ 2, 3 ^ 2, 4357 ^ 1, 9693389 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1520427451429 - 1) / 2 = 760213725714 from by norm_num]
      have h2 : (6 : ZMod 1520427451429) ^ 760213725714 = ((1520427451428 : ℕ) : ZMod 1520427451429) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1520427451429 - 1) / 3 = 506809150476 from by norm_num]
      have h2 : (6 : ZMod 1520427451429) ^ 506809150476 = ((365584371868 : ℕ) : ZMod 1520427451429) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1520427451429 - 1) / 4357 = 348962004 from by norm_num]
      have h2 : (6 : ZMod 1520427451429) ^ 348962004 = ((28353079180 : ℕ) : ZMod 1520427451429) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1520427451429 - 1) / 9693389 = 156852 from by norm_num]
      have h2 : (6 : ZMod 1520427451429) ^ 156852 = ((223859583799 : ℕ) : ZMod 1520427451429) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1475034311407732073353 : Nat.Prime 1475034311407732073353 := by
  refine lucas_primality 1475034311407732073353 (7 : ZMod 1475034311407732073353) ?_ (fun q hq hd => ?_)
  · rw [show 1475034311407732073353 - 1 = 1475034311407732073352 from by norm_num]
    reduce_mod_char
  · have e : 1475034311407732073353 - 1 = [2 ^ 3, 3 ^ 2, 61 ^ 1, 220889 ^ 1, 1520427451429 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1475034311407732073353 - 1) / 2 = 737517155703866036676 from by norm_num]
      have h2 : (7 : ZMod 1475034311407732073353) ^ 737517155703866036676 = ((1475034311407732073352 : ℕ) : ZMod 1475034311407732073353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1475034311407732073353 - 1) / 3 = 491678103802577357784 from by norm_num]
      have h2 : (7 : ZMod 1475034311407732073353) ^ 491678103802577357784 = ((161696189469382778925 : ℕ) : ZMod 1475034311407732073353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1475034311407732073353 - 1) / 61 = 24180890350946427432 from by norm_num]
      have h2 : (7 : ZMod 1475034311407732073353) ^ 24180890350946427432 = ((282111116711893098878 : ℕ) : ZMod 1475034311407732073353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1475034311407732073353 - 1) / 220889 = 6677717366676168 from by norm_num]
      have h2 : (7 : ZMod 1475034311407732073353) ^ 6677717366676168 = ((53130322698137690632 : ℕ) : ZMod 1475034311407732073353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1520427451429).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1475034311407732073353 - 1) / 1520427451429 = 970144488 from by norm_num]
      have h2 : (7 : ZMod 1475034311407732073353) ^ 970144488 = ((1120888090858768703711 : ℕ) : ZMod 1475034311407732073353) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 244: 3^2 divides 338867 + 1 (5^244+1 -> 1475034311407732073353 -> 338867).
theorem ke244 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 244 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g1475034311407732073353 : 1475034311407732073353 ∈ P := S7 1475034311407732073353 prime_1475034311407732073353 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1475034311407732073353 ∣ 1 + 5 ^ 244).trans hd)
  have g338867 : 338867 ∈ P := S1 338867 (by norm_num) (by norm_num) (hnz (by norm_num)) 1475034311407732073353 g1475034311407732073353 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 338867 g338867 (by norm_num)

-- e an odd multiple of 254: 13 divides 5^254 + 1 and 18797 + 1 (5^254+1 -> 18797).
theorem ke254 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 254 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g18797 : 18797 ∈ P := S7 18797 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 18797 ∣ 1 + 5 ^ 254).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 13 ∣ 1 + 5 ^ 254).trans hd) 18797 g18797 (by norm_num)

-- e an odd multiple of 256: 3^2 divides 17 + 1 (5^256+1 -> 1655809 -> 271 -> 17).
theorem ke256 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 256 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g1655809 : 1655809 ∈ P := S7 1655809 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1655809 ∣ 1 + 5 ^ 256).trans hd)
  have g271 : 271 ∈ P := S1 271 (by norm_num) (by norm_num) (hnz (by norm_num)) 1655809 g1655809 (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 271 g271 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 17 g17 (by norm_num)

-- e an odd multiple of 262: 7 divides 13 + 1 and 1049 + 1 (5^262+1 -> 13; 5^262+1 -> 1049).
theorem ke262 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 262 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 13 ∣ 1 + 5 ^ 262).trans hd)
  have g1049 : 1049 ∈ P := S7 1049 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 1049 ∣ 1 + 5 ^ 262).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 1049 g1049 (by norm_num) (by norm_num)) (by norm_num)

theorem prime_99406033 : Nat.Prime 99406033 := by
  refine lucas_primality 99406033 (5 : ZMod 99406033) ?_ (fun q hq hd => ?_)
  · rw [show 99406033 - 1 = 99406032 from by norm_num]
    reduce_mod_char
  · have e : 99406033 - 1 = [2 ^ 4, 3 ^ 1, 11 ^ 1, 59 ^ 1, 3191 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99406033 - 1) / 2 = 49703016 from by norm_num]
      have h2 : (5 : ZMod 99406033) ^ 49703016 = ((99406032 : ℕ) : ZMod 99406033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99406033 - 1) / 3 = 33135344 from by norm_num]
      have h2 : (5 : ZMod 99406033) ^ 33135344 = ((25452774 : ℕ) : ZMod 99406033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99406033 - 1) / 11 = 9036912 from by norm_num]
      have h2 : (5 : ZMod 99406033) ^ 9036912 = ((92987843 : ℕ) : ZMod 99406033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99406033 - 1) / 59 = 1684848 from by norm_num]
      have h2 : (5 : ZMod 99406033) ^ 1684848 = ((85650015 : ℕ) : ZMod 99406033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99406033 - 1) / 3191 = 31152 from by norm_num]
      have h2 : (5 : ZMod 99406033) ^ 31152 = ((71634082 : ℕ) : ZMod 99406033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_112835047682166217 : Nat.Prime 112835047682166217 := by
  refine lucas_primality 112835047682166217 (15 : ZMod 112835047682166217) ?_ (fun q hq hd => ?_)
  · rw [show 112835047682166217 - 1 = 112835047682166216 from by norm_num]
    reduce_mod_char
  · have e : 112835047682166217 - 1 = [2 ^ 3, 3 ^ 1, 11 ^ 1, 1109 ^ 1, 3877 ^ 1, 99406033 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (112835047682166217 - 1) / 2 = 56417523841083108 from by norm_num]
      have h2 : (15 : ZMod 112835047682166217) ^ 56417523841083108 = ((112835047682166216 : ℕ) : ZMod 112835047682166217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (112835047682166217 - 1) / 3 = 37611682560722072 from by norm_num]
      have h2 : (15 : ZMod 112835047682166217) ^ 37611682560722072 = ((26591953819672827 : ℕ) : ZMod 112835047682166217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (112835047682166217 - 1) / 11 = 10257731607469656 from by norm_num]
      have h2 : (15 : ZMod 112835047682166217) ^ 10257731607469656 = ((109309318402026182 : ℕ) : ZMod 112835047682166217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (112835047682166217 - 1) / 1109 = 101744858144424 from by norm_num]
      have h2 : (15 : ZMod 112835047682166217) ^ 101744858144424 = ((26882197643661859 : ℕ) : ZMod 112835047682166217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (112835047682166217 - 1) / 3877 = 29103700717608 from by norm_num]
      have h2 : (15 : ZMod 112835047682166217) ^ 29103700717608 = ((33041744143175292 : ℕ) : ZMod 112835047682166217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_99406033).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (112835047682166217 - 1) / 99406033 = 1135092552 from by norm_num]
      have h2 : (15 : ZMod 112835047682166217) ^ 1135092552 = ((41955527378129421 : ℕ) : ZMod 112835047682166217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_331660297 : Nat.Prime 331660297 := by
  refine lucas_primality 331660297 (7 : ZMod 331660297) ?_ (fun q hq hd => ?_)
  · rw [show 331660297 - 1 = 331660296 from by norm_num]
    reduce_mod_char
  · have e : 331660297 - 1 = [2 ^ 3, 3 ^ 2, 11 ^ 1, 418763 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (331660297 - 1) / 2 = 165830148 from by norm_num]
      have h2 : (7 : ZMod 331660297) ^ 165830148 = ((331660296 : ℕ) : ZMod 331660297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (331660297 - 1) / 3 = 110553432 from by norm_num]
      have h2 : (7 : ZMod 331660297) ^ 110553432 = ((75193899 : ℕ) : ZMod 331660297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (331660297 - 1) / 11 = 30150936 from by norm_num]
      have h2 : (7 : ZMod 331660297) ^ 30150936 = ((170828740 : ℕ) : ZMod 331660297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (331660297 - 1) / 418763 = 792 from by norm_num]
      have h2 : (7 : ZMod 331660297) ^ 792 = ((281180601 : ℕ) : ZMod 331660297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_901395700433 : Nat.Prime 901395700433 := by
  refine lucas_primality 901395700433 (3 : ZMod 901395700433) ?_ (fun q hq hd => ?_)
  · rw [show 901395700433 - 1 = 901395700432 from by norm_num]
    reduce_mod_char
  · have e : 901395700433 - 1 = [2 ^ 4, 17 ^ 1, 5897 ^ 1, 561973 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (901395700433 - 1) / 2 = 450697850216 from by norm_num]
      have h2 : (3 : ZMod 901395700433) ^ 450697850216 = ((901395700432 : ℕ) : ZMod 901395700433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (901395700433 - 1) / 17 = 53023276496 from by norm_num]
      have h2 : (3 : ZMod 901395700433) ^ 53023276496 = ((64167815880 : ℕ) : ZMod 901395700433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (901395700433 - 1) / 5897 = 152856656 from by norm_num]
      have h2 : (3 : ZMod 901395700433) ^ 152856656 = ((318802407868 : ℕ) : ZMod 901395700433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (901395700433 - 1) / 561973 = 1603984 from by norm_num]
      have h2 : (3 : ZMod 901395700433) ^ 1603984 = ((603711107101 : ℕ) : ZMod 901395700433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6509387183417404924784917 : Nat.Prime 6509387183417404924784917 := by
  refine lucas_primality 6509387183417404924784917 (14 : ZMod 6509387183417404924784917) ?_ (fun q hq hd => ?_)
  · rw [show 6509387183417404924784917 - 1 = 6509387183417404924784916 from by norm_num]
    reduce_mod_char
  · have e : 6509387183417404924784917 - 1 = [2 ^ 2, 3 ^ 1, 7 ^ 1, 11 ^ 1, 16451 ^ 1, 475073 ^ 1, 901395700433 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6509387183417404924784917 - 1) / 2 = 3254693591708702462392458 from by norm_num]
      have h2 : (14 : ZMod 6509387183417404924784917) ^ 3254693591708702462392458 = ((6509387183417404924784916 : ℕ) : ZMod 6509387183417404924784917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6509387183417404924784917 - 1) / 3 = 2169795727805801641594972 from by norm_num]
      have h2 : (14 : ZMod 6509387183417404924784917) ^ 2169795727805801641594972 = ((2384185791015624 : ℕ) : ZMod 6509387183417404924784917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6509387183417404924784917 - 1) / 7 = 929912454773914989254988 from by norm_num]
      have h2 : (14 : ZMod 6509387183417404924784917) ^ 929912454773914989254988 = ((3859770023058668457568528 : ℕ) : ZMod 6509387183417404924784917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6509387183417404924784917 - 1) / 11 = 591762471219764084071356 from by norm_num]
      have h2 : (14 : ZMod 6509387183417404924784917) ^ 591762471219764084071356 = ((5728260721311948902170102 : ℕ) : ZMod 6509387183417404924784917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6509387183417404924784917 - 1) / 16451 = 395683373862829306716 from by norm_num]
      have h2 : (14 : ZMod 6509387183417404924784917) ^ 395683373862829306716 = ((5940861322802300730589694 : ℕ) : ZMod 6509387183417404924784917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6509387183417404924784917 - 1) / 475073 = 13701867257068713492 from by norm_num]
      have h2 : (14 : ZMod 6509387183417404924784917) ^ 13701867257068713492 = ((2079617350031112141255855 : ℕ) : ZMod 6509387183417404924784917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_901395700433).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6509387183417404924784917 - 1) / 901395700433 = 7221453552852 from by norm_num]
      have h2 : (14 : ZMod 6509387183417404924784917) ^ 7221453552852 = ((4819321872110198485471511 : ℕ) : ZMod 6509387183417404924784917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3212240478767 : Nat.Prime 3212240478767 := by
  refine lucas_primality 3212240478767 (5 : ZMod 3212240478767) ?_ (fun q hq hd => ?_)
  · rw [show 3212240478767 - 1 = 3212240478766 from by norm_num]
    reduce_mod_char
  · have e : 3212240478767 - 1 = [2 ^ 1, 11 ^ 1, 157 ^ 1, 4507 ^ 1, 206347 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3212240478767 - 1) / 2 = 1606120239383 from by norm_num]
      have h2 : (5 : ZMod 3212240478767) ^ 1606120239383 = ((3212240478766 : ℕ) : ZMod 3212240478767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3212240478767 - 1) / 11 = 292021861706 from by norm_num]
      have h2 : (5 : ZMod 3212240478767) ^ 292021861706 = ((937572780559 : ℕ) : ZMod 3212240478767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3212240478767 - 1) / 157 = 20460130438 from by norm_num]
      have h2 : (5 : ZMod 3212240478767) ^ 20460130438 = ((638730271587 : ℕ) : ZMod 3212240478767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3212240478767 - 1) / 4507 = 712722538 from by norm_num]
      have h2 : (5 : ZMod 3212240478767) ^ 712722538 = ((28135986234 : ℕ) : ZMod 3212240478767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3212240478767 - 1) / 206347 = 15567178 from by norm_num]
      have h2 : (5 : ZMod 3212240478767) ^ 15567178 = ((785655641227 : ℕ) : ZMod 3212240478767) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_64244809575341 : Nat.Prime 64244809575341 := by
  refine lucas_primality 64244809575341 (3 : ZMod 64244809575341) ?_ (fun q hq hd => ?_)
  · rw [show 64244809575341 - 1 = 64244809575340 from by norm_num]
    reduce_mod_char
  · have e : 64244809575341 - 1 = [2 ^ 2, 5 ^ 1, 3212240478767 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64244809575341 - 1) / 2 = 32122404787670 from by norm_num]
      have h2 : (3 : ZMod 64244809575341) ^ 32122404787670 = ((64244809575340 : ℕ) : ZMod 64244809575341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64244809575341 - 1) / 5 = 12848961915068 from by norm_num]
      have h2 : (3 : ZMod 64244809575341) ^ 12848961915068 = ((34085010592785 : ℕ) : ZMod 64244809575341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3212240478767).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64244809575341 - 1) / 3212240478767 = 20 from by norm_num]
      have h2 : (3 : ZMod 64244809575341) ^ 20 = ((3486784401 : ℕ) : ZMod 64244809575341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2213895710934906295050485076049 : Nat.Prime 2213895710934906295050485076049 := by
  refine lucas_primality 2213895710934906295050485076049 (19 : ZMod 2213895710934906295050485076049) ?_ (fun q hq hd => ?_)
  · rw [show 2213895710934906295050485076049 - 1 = 2213895710934906295050485076048 from by norm_num]
    reduce_mod_char
  · have e : 2213895710934906295050485076049 - 1 = [2 ^ 4, 3 ^ 1, 11 ^ 1, 431 ^ 1, 21101 ^ 1, 7176371 ^ 1, 64244809575341 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2213895710934906295050485076049 - 1) / 2 = 1106947855467453147525242538024 from by norm_num]
      have h2 : (19 : ZMod 2213895710934906295050485076049) ^ 1106947855467453147525242538024 = ((2213895710934906295050485076048 : ℕ) : ZMod 2213895710934906295050485076049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2213895710934906295050485076049 - 1) / 3 = 737965236978302098350161692016 from by norm_num]
      have h2 : (19 : ZMod 2213895710934906295050485076049) ^ 737965236978302098350161692016 = ((957345246723917398182461087522 : ℕ) : ZMod 2213895710934906295050485076049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2213895710934906295050485076049 - 1) / 11 = 201263246448627845004589552368 from by norm_num]
      have h2 : (19 : ZMod 2213895710934906295050485076049) ^ 201263246448627845004589552368 = ((1624958460911232094643275908029 : ℕ) : ZMod 2213895710934906295050485076049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2213895710934906295050485076049 - 1) / 431 = 5136648981287485603365394608 from by norm_num]
      have h2 : (19 : ZMod 2213895710934906295050485076049) ^ 5136648981287485603365394608 = ((2168299231565656795458233274963 : ℕ) : ZMod 2213895710934906295050485076049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2213895710934906295050485076049 - 1) / 21101 = 104918994878674294822543248 from by norm_num]
      have h2 : (19 : ZMod 2213895710934906295050485076049) ^ 104918994878674294822543248 = ((476287962492749119186039933212 : ℕ) : ZMod 2213895710934906295050485076049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2213895710934906295050485076049 - 1) / 7176371 = 308497945679634775717488 from by norm_num]
      have h2 : (19 : ZMod 2213895710934906295050485076049) ^ 308497945679634775717488 = ((232244258111580896179424340603 : ℕ) : ZMod 2213895710934906295050485076049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_64244809575341).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2213895710934906295050485076049 - 1) / 64244809575341 = 34460304662256528 from by norm_num]
      have h2 : (19 : ZMod 2213895710934906295050485076049) ^ 34460304662256528 = ((287985647938857173633093073233 : ℕ) : ZMod 2213895710934906295050485076049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 : Nat.Prime 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 := by
  refine lucas_primality 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ?_ (fun q hq hd => ?_)
  · rw [show 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1 = 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390000 from by norm_num]
    reduce_mod_char
  · have e : 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 4, 7 ^ 1, 13 ^ 1, 23 ^ 1, 31 ^ 1, 67 ^ 1, 89 ^ 1, 199 ^ 1, 601 ^ 1, 1453 ^ 1, 5281 ^ 1, 390001 ^ 1, 595123 ^ 1, 12207031 ^ 1, 190771747 ^ 1, 331660297 ^ 1, 386478495679 ^ 1, 1030330938209 ^ 1, 112835047682166217 ^ 1, 6509387183417404924784917 ^ 1, 9080418348371887359375390001 ^ 1, 2213895710934906295050485076049 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 2 = 16840571794297960422282067174552746018706008598032759664660963298894799186852651105831270559823595190196754126885556671039218303345178859710504216256056861316203151345282745437500195000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 16840571794297960422282067174552746018706008598032759664660963298894799186852651105831270559823595190196754126885556671039218303345178859710504216256056861316203151345282745437500195000 = ((33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390000 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 3 = 11227047862865306948188044783035164012470672398688506443107308865929866124568434070554180373215730126797836084590371114026145535563452573140336144170704574210802100896855163625000130000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 11227047862865306948188044783035164012470672398688506443107308865929866124568434070554180373215730126797836084590371114026145535563452573140336144170704574210802100896855163625000130000 = ((16009433767121323284550575663460537741604284989306453519741644063135662719134280492440903220904201679238446099052296060894205272211055891041142303550490695262759996267639555698520421276 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 5 = 6736228717719184168912826869821098407482403439213103865864385319557919674741060442332508223929438076078701650754222668415687321338071543884201686502422744526481260538113098175000078000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 6736228717719184168912826869821098407482403439213103865864385319557919674741060442332508223929438076078701650754222668415687321338071543884201686502422744526481260538113098175000078000 = ((20283434973537818199078208656277717808542507862639080917082170357348912487289454741622412121212363369638060535110929526511468219878174616125801358507088726265237478739587264618944562406 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 7 = 4811591941227988692080590621300784576773145313723645618474560942541371196243614601666077302806741482913358321967301906011205229527193959917286918930301960376058043241509355839285770000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 4811591941227988692080590621300784576773145313723645618474560942541371196243614601666077302806741482913358321967301906011205229527193959917286918930301960376058043241509355839285770000 = ((32440403494259776030148617913940728917244147314892973333055968407360450753322224561059740998890426540988709612035724619846291817532188265925427500815694894529294327854477055226977779996 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 13 = 2590857199122763141889548796085037849031693630466578409947840507522276797977330939358657009203630029261039096443931795544495123591565978417000648654777978664031254053120422375000030000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 2590857199122763141889548796085037849031693630466578409947840507522276797977330939358657009203630029261039096443931795544495123591565978417000648654777978664031254053120422375000030000 = ((11410790646896213018370415572978833152346613638494291791376667416095256321469160339995138131132056656848028893530534907852512332494109614184122156305025386375783755159494009256871354626 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 23 = 1464397547330257428024527580395890958148348573741979101274866373816939059726317487463588744332486538277978619729178840959932026377841639974826453587483205331843752290894151777173930000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 1464397547330257428024527580395890958148348573741979101274866373816939059726317487463588744332486538277978619729178840959932026377841639974826453587483205331843752290894151777173930000 = ((33392640524718937614142936582833518194003759164279100816168316695007430014268253694499356717378447827358406931329840179051584024527428353372804061466304265907091328073182899330580207539 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 31 = 1086488502857932930469810785455015872174581199873081268687804083799664463667912974569759390956360980012693814637777849744465696990011539336161562339100442665561493635179531963709690000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 1086488502857932930469810785455015872174581199873081268687804083799664463667912974569759390956360980012693814637777849744465696990011539336161562339100442665561493635179531963709690000 = ((5903981494490027591135626550017337351268048968812019527537262958905245795828691457208111192053182847645412071902066859161227711205487598628805616271663440958215521088258935522929138619 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 67 = 502703635650685385739763199240380478170328614866649542228685471608799975726944809129291658502196871349156839608524079732513979204333697304791170634509160039289646308814410311567170000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 502703635650685385739763199240380478170328614866649542228685471608799975726944809129291658502196871349156839608524079732513979204333697304791170634509160039289646308814410311567170000 = ((33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508250689625431058859241800793011285124722851151085487785190306663417968506249376 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 89 = 378439815602201357804091397180960584690022665124331677857549737053815712064104519232163383366822363824646160154731610585150973108880423813719195870922626096993329243714218998595510000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 378439815602201357804091397180960584690022665124331677857549737053815712064104519232163383366822363824646160154731610585150973108880423813719195870922626096993329243714218998595510000 = ((26309366326916102000633430108641783838540122569120111757379775151642599487319719364789543542018748955240184201469185059399946213782222715889995171501746207762206567484433949572322656332 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 199 = 169251977832140305751578564568369306720663402995304117232773500491405016953292975938002719194206986836148282682266901216474555812514360399100544886995546344886463832615906989321610000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 169251977832140305751578564568369306720663402995304117232773500491405016953292975938002719194206986836148282682266901216474555812514360399100544886995546344886463832615906989321610000 = ((32116201125638417549626806937858846763154014683709336497759818831039234282818573555075983974911602778360701486149209160287112175678375381418477015361247658391163088267586019052404314598 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 601 = 56041836253903362470156629532621450977391043587463426504695385354059231903003830635045825490261548053899348175991869121594736450399929649618982416825480403714486360550025775166390000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 56041836253903362470156629532621450977391043587463426504695385354059231903003830635045825490261548053899348175991869121594736450399929649618982416825480403714486360550025775166390000 = ((22210290911710000841793059293984026635769806080794709470363956485466438333379702263663829755420688514829683090764390329626655690906965439977354447420206118345772686492544530569961967428 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 1453 = 23180415408531260044435054610533717850937382791511025002974484926214451736892843917180000770576180578385071062471516408863342468472372828231939733318729334227395941287381617945630000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 23180415408531260044435054610533717850937382791511025002974484926214451736892843917180000770576180578385071062471516408863342468472372828231939733318729334227395941287381617945630000 = ((8586189667213932256619723899672890004078055826841946558029037075995244596987357169478547212984164624061252583941612145393234122867955968653147437564391764078057088178338791654645937557 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 5281 = 6377796551523560091756132238043077454537401476247968060844901836354780983470043971153671865110242450368018983861221992440529560062555902181595991765217519907670195548298710637190000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 6377796551523560091756132238043077454537401476247968060844901836354780983470043971153671865110242450368018983861221992440529560062555902181595991765217519907670195548298710637190000 = ((13773883145255545694831897613099387986986972863978721676066651318889440733277323275039758911397814505387384144999321774188069037084459379347872383309752274189373921038843120572845710990 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 390001 = 86361685197206983686103713449723185421093836159562460940669194688704896586689014160636873032754250323444063614634612070426579949001047995828237446858120165416002273559722900390000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 86361685197206983686103713449723185421093836159562460940669194688704896586689014160636873032754250323444063614634612070426579949001047995828237446858120165416002273559722900390000 = ((28578431042971244721420830969977785839178932342540821541277338680112478032988221692603078940241546653981409542780644837964182535871162970775577909134492831231778561814627347042947261004 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 595123 = 56595264489182775400319151417615336724361211373221198524207477442124734506489082444574552016385168075160106824591073344633691869899764787146536820980055757603732846303311232930000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 56595264489182775400319151417615336724361211373221198524207477442124734506489082444574552016385168075160106824591073344633691869899764787146536820980055757603732846303311232930000 = ((10379954651816459446752220348331337024588768369210106358656045198756446098487123026475457554057699901793459781479505750326384910022130387245559946718874425047464798906734290795994313623 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 12207031 = 2759159339285361104150889298888934748950176107201294018940553734793464387344089009986338293041706077455976662447331651904417757822549784580788599005942863799756574935425779690000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 2759159339285361104150889298888934748950176107201294018940553734793464387344089009986338293041706077455976662447331651904417757822549784580788599005942863799756574935425779690000 = ((15576915927421838228031976566466500775058131005468527973830224796120904561003781762412703358997447752689760707522206300492012942139098528305351939012407496187149457055863295221237931008 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_190771747).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 190771747 = 176552053007073006699278873559329998888210722293514035541761467424154785214108786306090393561511969486726502817899514974187643239909931313995926412059924799202086788514682370000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 176552053007073006699278873559329998888210722293514035541761467424154785214108786306090393561511969486726502817899514974187643239909931313995926412059924799202086788514682370000 = ((913940586935494049241751536010504067112229368433806261222272347104491965780461954350906789388903795550910319380246464585490875529593029665050163554107822331421768653781389256179585324 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_331660297).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 331660297 = 101553137029832427740255368429298282988066000544121563424041457087007307280151480451887013535561027313418549624500617697024002263045545422704027888246490120680336671985086870000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 101553137029832427740255368429298282988066000544121563424041457087007307280151480451887013535561027313418549624500617697024002263045545422704027888246490120680336671985086870000 = ((6503232135773848989823848535481015707702309810966691040555835661445908679534362265896434583534269154856348094548513704294951268277137189281623408524455531740175349115568029040756498715 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_386478495679).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 386478495679 = 87148816726327487606749685423305262133635001366188184420662653884945542405476607225827467614492599051735164456286077900039922564289768045873434508598083035109904166468410000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 87148816726327487606749685423305262133635001366188184420662653884945542405476607225827467614492599051735164456286077900039922564289768045873434508598083035109904166468410000 = ((1232567249839444529583835625865969875557579239999520827598088034226541210997676867181741976467452799560789483528080629178744436900946550759408732933251191435459326405907947721738281685 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1030330938209).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 1030330938209 = 32689636251380609196096552646778148609020400139416424764471057572004255725024548146813398470388540443965881669936076473578430606839125821330652050995684499162645004808710000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 32689636251380609196096552646778148609020400139416424764471057572004255725024548146813398470388540443965881669936076473578430606839125821330652050995684499162645004808710000 = ((3539190638291380503100097446559159030170985644155648383438344274969531157929715797689686875054111334590144195782157385469988525081347304898502013459816694613461333353506366165724624235 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_112835047682166217).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 112835047682166217 = 298498952944735507007790792766930450325102529497629461215123405522405123297633673253109144225017622195928541262887120049201800081684832267653288771240891617180155670000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 298498952944735507007790792766930450325102529497629461215123405522405123297633673253109144225017622195928541262887120049201800081684832267653288771240891617180155670000 = ((3865307595346526015881793377936795801852931637417364556937431302617864407578012314426563448578991636076543695497632941582454142059544515944870583194841214009987956285872515459999045179 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6509387183417404924784917).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 6509387183417404924784917 = 5174241850968441127669465050912389209481801652426971331698820673133963167264120052838093842682084396787126367384206553818243649616600562172452093789371818670000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 5174241850968441127669465050912389209481801652426971331698820673133963167264120052838093842682084396787126367384206553818243649616600562172452093789371818670000 = ((10834261194069421692428521599735746801632907771159131052711009197900037010628284272473215112278557261309074993988439216950575632612625353022383801911692058074814576947136331218889720739 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_9080418348371887359375390001).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 9080418348371887359375390001 = 3709206150687421385731735261546986982920764926305119973042113518956381421158836912414463682167396100517279546818910640482162222042461507953703403472900390000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 3709206150687421385731735261546986982920764926305119973042113518956381421158836912414463682167396100517279546818910640482162222042461507953703403472900390000 = ((24481213539615587945788373136733868757289285540090723210632722069700313240542751961839572949089765276803069949984427240141884285507930509905771369702113706455364275102402526869785903552 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2213895710934906295050485076049).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 - 1) / 2213895710934906295050485076049 = 15213518605342392813328074534187849407010281062107653032524066915898960353221988765138334537929809200488482334577957351014735555170029021803909179115110000 from by norm_num]
      have h2 : (11 : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) ^ 15213518605342392813328074534187849407010281062107653032524066915898960353221988765138334537929809200488482334577957351014735555170029021803909179115110000 = ((7030413325482784282489839691425912282002330613624674864986519793643868147005209838977165546251559963584123571390193403395961907750656255107015552573716507434728395946619739584431264858 : ℕ) : ZMod 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_14353064261093 : Nat.Prime 14353064261093 := by
  refine lucas_primality 14353064261093 (2 : ZMod 14353064261093) ?_ (fun q hq hd => ?_)
  · rw [show 14353064261093 - 1 = 14353064261092 from by norm_num]
    reduce_mod_char
  · have e : 14353064261093 - 1 = [2 ^ 2, 293 ^ 1, 101599 ^ 1, 120539 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14353064261093 - 1) / 2 = 7176532130546 from by norm_num]
      have h2 : (2 : ZMod 14353064261093) ^ 7176532130546 = ((14353064261092 : ℕ) : ZMod 14353064261093) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14353064261093 - 1) / 293 = 48986567444 from by norm_num]
      have h2 : (2 : ZMod 14353064261093) ^ 48986567444 = ((3280517725442 : ℕ) : ZMod 14353064261093) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14353064261093 - 1) / 101599 = 141271708 from by norm_num]
      have h2 : (2 : ZMod 14353064261093) ^ 141271708 = ((2454952430424 : ℕ) : ZMod 14353064261093) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14353064261093 - 1) / 120539 = 119074028 from by norm_num]
      have h2 : (2 : ZMod 14353064261093) ^ 119074028 = ((13207633794329 : ℕ) : ZMod 14353064261093) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 268: 13^2 divides 14353064261093 + 1 (5^268+1 -> 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 -> 14353064261093).
theorem ke268 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 268 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 : 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 ∈ P := S7 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 prime_33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 ∣ 1 + 5 ^ 268).trans hd)
  have g14353064261093 : 14353064261093 ∈ P := S1 14353064261093 prime_14353064261093 (by norm_num) (hnz (by norm_num)) 33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 g33681143588595920844564134349105492037412017196065519329321926597789598373705302211662541119647190380393508253771113342078436606690357719421008432512113722632406302690565490875000390001 (by norm_num)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 14353064261093 g14353064261093 (by norm_num)

-- e an odd multiple of 271: 3 divides 5^271 + 1 and 412463 + 1 (5^271+1 -> 412463).
theorem ke271 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 271 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g412463 : 412463 ∈ P := S7 412463 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 412463 ∣ 1 + 5 ^ 271).trans hd)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 3 ∣ 1 + 5 ^ 271).trans hd) 412463 g412463 (by norm_num)

theorem prime_21450226849 : Nat.Prime 21450226849 := by
  refine lucas_primality 21450226849 (11 : ZMod 21450226849) ?_ (fun q hq hd => ?_)
  · rw [show 21450226849 - 1 = 21450226848 from by norm_num]
    reduce_mod_char
  · have e : 21450226849 - 1 = [2 ^ 5, 3 ^ 1, 109 ^ 1, 127 ^ 1, 16141 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21450226849 - 1) / 2 = 10725113424 from by norm_num]
      have h2 : (11 : ZMod 21450226849) ^ 10725113424 = ((21450226848 : ℕ) : ZMod 21450226849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21450226849 - 1) / 3 = 7150075616 from by norm_num]
      have h2 : (11 : ZMod 21450226849) ^ 7150075616 = ((18410978297 : ℕ) : ZMod 21450226849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21450226849 - 1) / 109 = 196791072 from by norm_num]
      have h2 : (11 : ZMod 21450226849) ^ 196791072 = ((12237317471 : ℕ) : ZMod 21450226849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21450226849 - 1) / 127 = 168899424 from by norm_num]
      have h2 : (11 : ZMod 21450226849) ^ 168899424 = ((17897206729 : ℕ) : ZMod 21450226849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21450226849 - 1) / 16141 = 1328928 from by norm_num]
      have h2 : (11 : ZMod 21450226849) ^ 1328928 = ((10610748028 : ℕ) : ZMod 21450226849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_16945508997411292389468001 : Nat.Prime 16945508997411292389468001 := by
  refine lucas_primality 16945508997411292389468001 (29 : ZMod 16945508997411292389468001) ?_ (fun q hq hd => ?_)
  · rw [show 16945508997411292389468001 - 1 = 16945508997411292389468000 from by norm_num]
    reduce_mod_char
  · have e : 16945508997411292389468001 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 3, 13 ^ 1, 137 ^ 1, 36963881 ^ 1, 21450226849 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16945508997411292389468001 - 1) / 2 = 8472754498705646194734000 from by norm_num]
      have h2 : (29 : ZMod 16945508997411292389468001) ^ 8472754498705646194734000 = ((16945508997411292389468000 : ℕ) : ZMod 16945508997411292389468001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16945508997411292389468001 - 1) / 3 = 5648502999137097463156000 from by norm_num]
      have h2 : (29 : ZMod 16945508997411292389468001) ^ 5648502999137097463156000 = ((11649461245861738646834207 : ℕ) : ZMod 16945508997411292389468001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16945508997411292389468001 - 1) / 5 = 3389101799482258477893600 from by norm_num]
      have h2 : (29 : ZMod 16945508997411292389468001) ^ 3389101799482258477893600 = ((2250018953848248955089516 : ℕ) : ZMod 16945508997411292389468001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16945508997411292389468001 - 1) / 13 = 1303500692108560953036000 from by norm_num]
      have h2 : (29 : ZMod 16945508997411292389468001) ^ 1303500692108560953036000 = ((3465781576711093130333892 : ℕ) : ZMod 16945508997411292389468001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16945508997411292389468001 - 1) / 137 = 123689846696432791164000 from by norm_num]
      have h2 : (29 : ZMod 16945508997411292389468001) ^ 123689846696432791164000 = ((12274790630072998832659822 : ℕ) : ZMod 16945508997411292389468001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16945508997411292389468001 - 1) / 36963881 = 458434248216828000 from by norm_num]
      have h2 : (29 : ZMod 16945508997411292389468001) ^ 458434248216828000 = ((16337592199493911848505227 : ℕ) : ZMod 16945508997411292389468001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_21450226849).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16945508997411292389468001 - 1) / 21450226849 = 789992064732000 from by norm_num]
      have h2 : (29 : ZMod 16945508997411292389468001) ^ 789992064732000 = ((1604552472926057482327921 : ℕ) : ZMod 16945508997411292389468001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- e an odd multiple of 274: 41^2 divides 16945508997411292389468001 + 1 (5^274+1 -> 16945508997411292389468001).
theorem ke274 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 274 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g16945508997411292389468001 : 16945508997411292389468001 ∈ P := S7 16945508997411292389468001 prime_16945508997411292389468001 (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 16945508997411292389468001 ∣ 1 + 5 ^ 274).trans hd)
  exact S6 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 16945508997411292389468001 g16945508997411292389468001 (by norm_num)

-- e an odd multiple of 277: 3^2 divides 9650681 + 1 (5^277+1 -> 9650681).
theorem ke277 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 277 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g9650681 : 9650681 ∈ P := S7 9650681 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 9650681 ∣ 1 + 5 ^ 277).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 9650681 g9650681 (by norm_num)

-- e an odd multiple of 278: 3^2 divides 557 + 1 (5^278+1 -> 557).
theorem ke278 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 278 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g557 : 557 ∈ P := S7 557 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 557 ∣ 1 + 5 ^ 278).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 557 g557 (by norm_num)

-- e an odd multiple of 283: 3 divides 5^283 + 1 and 1031 + 1 (5^283+1 -> 28867 -> 1031).
theorem ke283 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 283 ∣ 1 + 5 ^ e) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (hK5 e) E
  have g28867 : 28867 ∈ P := S7 28867 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 28867 ∣ 1 + 5 ^ 283).trans hd)
  have g1031 : 1031 ∈ P := S1 1031 (by norm_num) (by norm_num) (hnz (by norm_num)) 28867 g28867 (by norm_num)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [← ZMod.natCast_eq_zero_iff]; push_cast; reduce_mod_char : 3 ∣ 1 + 5 ^ 283).trans hd) 1031 g1031 (by norm_num)

-- The exponent sieve: e is no odd multiple of any d with 3 <= d <= 283, d != 4.
theorem esieve {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p) :
    ∀ d, 3 ≤ d → d ≤ 283 → d ≠ 4 → e % (2 * d) ≠ d := by
  obtain ⟨r5, r6, r7, r8, r10, r12, r13, r14, r16, r19, r20, r22, r26, r28, r29, r31, r32, r34, r37, r38⟩ := core5_residues hP E
  have M : ∀ t, t % 2 = 1 → t % 6 ≠ 1 → e % (2 * t) ≠ t := fun t h1 h2 h =>
    h2 (odd_divisor_mod_six hP E h1 (one_add_pow_dvd_of_odd_mul h))
  intro d lo hi h4 
  interval_cases d
  · exact M 3 (by norm_num) (by norm_num)
  · exact absurd rfl h4
  · exact M 5 (by norm_num) (by norm_num)
  · exact r6
  · exact r7
  · exact r8
  · exact M 9 (by norm_num) (by norm_num)
  · exact r10
  · exact M 11 (by norm_num) (by norm_num)
  · exact r12
  · exact r13
  · exact r14
  · exact M 15 (by norm_num) (by norm_num)
  · exact r16
  · exact M 17 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact r19
  · exact r20
  · exact M 21 (by norm_num) (by norm_num)
  · exact r22
  · exact M 23 (by norm_num) (by norm_num)
  · exact fun h => r8 (by omega)
  · exact fun h => M 5 (by norm_num) (by norm_num) (by omega)
  · exact r26
  · exact M 27 (by norm_num) (by norm_num)
  · exact r28
  · exact M 29 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact r31
  · exact r32
  · exact M 33 (by norm_num) (by norm_num)
  · exact r34
  · exact M 35 (by norm_num) (by norm_num)
  · exact fun h => r12 (by omega)
  · exact r37
  · exact r38
  · exact M 39 (by norm_num) (by norm_num)
  · exact fun h => r8 (by omega)
  · exact M 41 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => ke43 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => ke44 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 45 (by norm_num) (by norm_num)
  · exact fun h => ke46 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 47 (by norm_num) (by norm_num)
  · exact fun h => r16 (by omega)
  · exact fun h => r7 (by omega)
  · exact fun h => r10 (by omega)
  · exact M 51 (by norm_num) (by norm_num)
  · exact fun h => ke52 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 53 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => M 5 (by norm_num) (by norm_num) (by omega)
  · exact fun h => r8 (by omega)
  · exact M 57 (by norm_num) (by norm_num)
  · exact fun h => ke58 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 59 (by norm_num) (by norm_num)
  · exact fun h => r12 (by omega)
  · exact fun h => ke61 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => ke62 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 63 (by norm_num) (by norm_num)
  · exact fun h => ke64 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 65 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => ke67 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => ke68 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 69 (by norm_num) (by norm_num)
  · exact fun h => r10 (by omega)
  · exact M 71 (by norm_num) (by norm_num)
  · exact fun h => r8 (by omega)
  · exact fun h => ke73 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => ke74 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 75 (by norm_num) (by norm_num)
  · exact fun h => ke76 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 77 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => ke79 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => r16 (by omega)
  · exact M 81 (by norm_num) (by norm_num)
  · exact fun h => ke82 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 83 (by norm_num) (by norm_num)
  · exact fun h => r12 (by omega)
  · exact fun h => M 5 (by norm_num) (by norm_num) (by omega)
  · exact fun h => ke86 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 87 (by norm_num) (by norm_num)
  · exact fun h => r8 (by omega)
  · exact M 89 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => r7 (by omega)
  · exact fun h => ke92 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 93 (by norm_num) (by norm_num)
  · exact fun h => ke94 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 95 (by norm_num) (by norm_num)
  · exact fun h => r32 (by omega)
  · exact fun h => ke97 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => r14 (by omega)
  · exact M 99 (by norm_num) (by norm_num)
  · exact fun h => r20 (by omega)
  · exact M 101 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => ke103 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => r8 (by omega)
  · exact M 105 (by norm_num) (by norm_num)
  · exact fun h => ke106 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 107 (by norm_num) (by norm_num)
  · exact fun h => r12 (by omega)
  · exact fun h => ke109 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => r10 (by omega)
  · exact M 111 (by norm_num) (by norm_num)
  · exact fun h => r16 (by omega)
  · exact M 113 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => M 5 (by norm_num) (by norm_num) (by omega)
  · exact fun h => ke116 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 117 (by norm_num) (by norm_num)
  · exact fun h => ke118 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 119 (by norm_num) (by norm_num)
  · exact fun h => r8 (by omega)
  · exact fun h => M 11 (by norm_num) (by norm_num) (by omega)
  · exact fun h => ke122 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 123 (by norm_num) (by norm_num)
  · exact fun h => ke124 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 125 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => ke127 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => ke128 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 129 (by norm_num) (by norm_num)
  · exact fun h => r10 (by omega)
  · exact M 131 (by norm_num) (by norm_num)
  · exact fun h => r12 (by omega)
  · exact fun h => r7 (by omega)
  · exact fun h => ke134 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 135 (by norm_num) (by norm_num)
  · exact fun h => r8 (by omega)
  · exact M 137 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => ke139 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => r20 (by omega)
  · exact M 141 (by norm_num) (by norm_num)
  · exact fun h => ke142 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 143 (by norm_num) (by norm_num)
  · exact fun h => r16 (by omega)
  · exact fun h => M 5 (by norm_num) (by norm_num) (by omega)
  · exact fun h => ke146 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 147 (by norm_num) (by norm_num)
  · exact fun h => ke148 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 149 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => ke151 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => r8 (by omega)
  · exact M 153 (by norm_num) (by norm_num)
  · exact fun h => r14 (by omega)
  · exact M 155 (by norm_num) (by norm_num)
  · exact fun h => r12 (by omega)
  · exact fun h => ke157 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => ke158 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 159 (by norm_num) (by norm_num)
  · exact fun h => r32 (by omega)
  · exact M 161 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => ke163 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => ke164 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 165 (by norm_num) (by norm_num)
  · exact fun h => ke166 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 167 (by norm_num) (by norm_num)
  · exact fun h => r8 (by omega)
  · exact fun h => r13 (by omega)
  · exact fun h => r10 (by omega)
  · exact M 171 (by norm_num) (by norm_num)
  · exact fun h => ke172 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 173 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => M 5 (by norm_num) (by norm_num) (by omega)
  · exact fun h => r16 (by omega)
  · exact M 177 (by norm_num) (by norm_num)
  · exact fun h => ke178 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 179 (by norm_num) (by norm_num)
  · exact fun h => r12 (by omega)
  · exact fun h => ke181 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => r14 (by omega)
  · exact M 183 (by norm_num) (by norm_num)
  · exact fun h => r8 (by omega)
  · exact M 185 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => M 11 (by norm_num) (by norm_num) (by omega)
  · exact fun h => ke188 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 189 (by norm_num) (by norm_num)
  · exact fun h => r10 (by omega)
  · exact M 191 (by norm_num) (by norm_num)
  · exact fun h => ke64 hP E (one_add_pow_dvd_of_odd_mul (e0 := 64) (by omega))
  · exact fun h => ke193 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => ke194 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 195 (by norm_num) (by norm_num)
  · exact fun h => r28 (by omega)
  · exact M 197 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => ke199 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => r8 (by omega)
  · exact M 201 (by norm_num) (by norm_num)
  · exact fun h => ke202 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 203 (by norm_num) (by norm_num)
  · exact fun h => r12 (by omega)
  · exact fun h => M 5 (by norm_num) (by norm_num) (by omega)
  · exact fun h => ke206 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 207 (by norm_num) (by norm_num)
  · exact fun h => r16 (by omega)
  · exact M 209 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => ke211 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => ke212 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 213 (by norm_num) (by norm_num)
  · exact fun h => ke214 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 215 (by norm_num) (by norm_num)
  · exact fun h => r8 (by omega)
  · exact fun h => r7 (by omega)
  · exact fun h => ke218 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 219 (by norm_num) (by norm_num)
  · exact fun h => r20 (by omega)
  · exact M 221 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => ke223 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => r32 (by omega)
  · exact M 225 (by norm_num) (by norm_num)
  · exact fun h => ke226 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 227 (by norm_num) (by norm_num)
  · exact fun h => r12 (by omega)
  · exact fun h => ke229 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => r10 (by omega)
  · exact M 231 (by norm_num) (by norm_num)
  · exact fun h => r8 (by omega)
  · exact M 233 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => M 5 (by norm_num) (by norm_num) (by omega)
  · exact fun h => ke236 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 237 (by norm_num) (by norm_num)
  · exact fun h => r14 (by omega)
  · exact M 239 (by norm_num) (by norm_num)
  · exact fun h => r16 (by omega)
  · exact fun h => ke241 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => r22 (by omega)
  · exact M 243 (by norm_num) (by norm_num)
  · exact fun h => ke244 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 245 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => r13 (by omega)
  · exact fun h => r8 (by omega)
  · exact M 249 (by norm_num) (by norm_num)
  · exact fun h => r10 (by omega)
  · exact M 251 (by norm_num) (by norm_num)
  · exact fun h => r12 (by omega)
  · exact fun h => M 11 (by norm_num) (by norm_num) (by omega)
  · exact fun h => ke254 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 255 (by norm_num) (by norm_num)
  · exact fun h => ke256 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 257 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => r7 (by omega)
  · exact fun h => r20 (by omega)
  · exact M 261 (by norm_num) (by norm_num)
  · exact fun h => ke262 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 263 (by norm_num) (by norm_num)
  · exact fun h => r8 (by omega)
  · exact fun h => M 5 (by norm_num) (by norm_num) (by omega)
  · exact fun h => r14 (by omega)
  · exact M 267 (by norm_num) (by norm_num)
  · exact fun h => ke268 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 269 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => ke271 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => r16 (by omega)
  · exact M 273 (by norm_num) (by norm_num)
  · exact fun h => ke274 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 275 (by norm_num) (by norm_num)
  · exact fun h => r12 (by omega)
  · exact fun h => ke277 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact fun h => ke278 hP E (one_add_pow_dvd_of_odd_mul h)
  · exact M 279 (by norm_num) (by norm_num)
  · exact fun h => r8 (by omega)
  · exact M 281 (by norm_num) (by norm_num)
  · exact fun h => r6 (by omega)
  · exact fun h => ke283 hP E (one_add_pow_dvd_of_odd_mul h)

-- Section 3. The step.
theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.H3 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max A1 A2, fun n h hS he _ _ _ _ _ a147 hR => ?_⟩
  obtain ⟨hP, _, E⟩ := setup h hS
  have sv := esieve hP E
  have hN : 283 < n.factorization 5 := by
    by_contra hle
    exact sv (n.factorization 5) (by omega) (by omega) (by omega) (Nat.mod_eq_of_lt (by omega))
  rcases Nat.even_or_odd (n.factorization 5) with hev | hod
  · exact (h2 n h hS hN hev sv
      (fun ha d hd => odd_two_divisor_mod_six hP E (Nat.odd_iff.mp ha) hd) a147 hR).trans
      (le_max_right _ _)
  · have ho : n.factorization 5 % 2 = 1 := Nat.odd_iff.mp hod
    have hae : padicValNat 2 n % 2 = 0 := by
      by_contra hne
      exact not_odd_odd hP E (by omega) ho
    exact (h1 n h hS hN hod
      (fun d hd => odd_divisor_mod_six hP E (odd_of_dvd_odd hd ho)
        (one_add_pow_dvd_of_odd_mul (mod_of_dvd_odd hd ho)))
      (fun d lo hi hd => sv d lo hi (fun h4 => by subst h4; omega) (mod_of_dvd_odd hd ho))
      (Nat.even_iff.mpr hae) hR).trans (le_max_left _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H3_R1
