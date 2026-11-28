import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1.H1.R1.H1.R1
-- Credit: @adammcarter
-- Splits step H1 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1.H1.R1 (3 is the only repeated
-- odd prime, e(3) = 11, a = padicValNat 2 n odd) after closing the open sieve classes 269, 271,
-- 311, 313, 347, 353, 383 and sieving odd primes up to 991.  Proving H1 and H2 proves the step.
--
-- Notation as in the parent: balance equation (2^a + 1)(1 + 3^11) prod_P (p + 1) =
-- 2^(a+1) 3^11 prod_P p, every odd prime other than 3 simple, 1 + 3^11 = 4 * 67 * 661 forcing the
-- simple primes 67, 661, 17, 331, 83, 7.  For a odd, a is an odd multiple of an odd d iff d | a.
--
-- PROVED BELOW (nsieve, lemmas kn_d<d>): a is no odd multiple of any d in the list of the
-- hypotheses: the seven parent exceptions 269, 271, 311, 313, 347, 353, 383 and 66 primes from
-- 401 to 991.  Each chain starts at prime factors of 2^d + 1 (full factorisations from factordb,
-- re-checked by divisibility in Lean; PARI and GMP-ECM for the p + 1 and p - 1) and ends at a prime
-- with two sources (kernel 1 + 3^11, 2^d + 1 or some p + 1), a square, or more than 11 factors of 3.
-- 142 Lucas certificates (up to 104 digits).  Together with the parent sieve: for a odd, every
-- divisor d <= 400 of a lies in {1, 3, 5, 7, 9, 11, 13}, and no listed prime from 401 to 991
-- divides a.  Odd primes 401..991 NOT excluded: 409, 419, 421, 433, 449, 503, 613, 617, 619, 631,
-- 701, 739, 751, 811, 827, 853, 863, 883, 911, 937, 953, 977, 983, 997 (no certificate within the
-- size budget, none found, or not searched).
--
-- H1 (OPEN): a odd and one of 3, 5, 7, 11, 13 divides a.
-- H2 (OPEN): a odd and none of 3, 5, 7, 11, 13 divides a (so every prime factor of a is > 400).

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts S_sq zmod_ne_one prime_dvd_prime_pow
  kernel_balance_one)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 (budget_kernel3 two_pow_add_one_dvd_of_odd_mul)

-- H1: a odd, divisible by one of 3, 5, 7, 11, 13.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    padicValNat 2 n % 2 = 1 →
    262 ≤ padicValNat 2 n →
    (∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 2, 3, 5, 7, 8, 9, 11, 13, 269, 271, 311, 313, 347, 353, 383} : Finset ℕ) →
      padicValNat 2 n % (2 * d) ≠ d) →
    (((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 7) →
    (∀ d ∈ ({269, 271, 311, 313, 347, 353, 383, 401, 431, 439, 443, 457, 461, 463, 467, 479, 487, 491, 499, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 709, 719, 727, 733, 743, 757, 761, 769, 773, 787, 797, 809, 821, 823, 829, 839, 857, 859, 877, 881, 887, 907, 919, 929, 941, 947, 967, 971, 991} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (3 ∣ padicValNat 2 n ∨ 5 ∣ padicValNat 2 n ∨ 7 ∣ padicValNat 2 n ∨ 11 ∣ padicValNat 2 n ∨
      13 ∣ padicValNat 2 n) →
    padicValNat 2 n ≤ A

-- H2: a odd, divisible by none of 3, 5, 7, 11, 13.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    padicValNat 2 n % 2 = 1 →
    262 ≤ padicValNat 2 n →
    (∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 2, 3, 5, 7, 8, 9, 11, 13, 269, 271, 311, 313, 347, 353, 383} : Finset ℕ) →
      padicValNat 2 n % (2 * d) ≠ d) →
    (((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 7) →
    (∀ d ∈ ({269, 271, 311, 313, 347, 353, 383, 401, 431, 439, 443, 457, 461, 463, 467, 479, 487, 491, 499, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 709, 719, 727, 733, 743, 757, 761, 769, 773, 787, 797, 809, 821, 823, 829, 839, 857, 859, 877, 881, 887, 907, 919, 929, 941, 947, 967, 971, 991} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    ¬ 3 ∣ padicValNat 2 n → ¬ 5 ∣ padicValNat 2 n → ¬ 7 ∣ padicValNat 2 n →
    ¬ 11 ∣ padicValNat 2 n → ¬ 13 ∣ padicValNat 2 n →
    padicValNat 2 n ≤ A

-- Section 1. Lucas certificates and chain lemmas.

theorem prime_369054083513 : Nat.Prime 369054083513 := by
  refine lucas_primality 369054083513 (3 : ZMod 369054083513) ?_ (fun q hq hd => ?_)
  · rw [show 369054083513 - 1 = 369054083512 from by norm_num]
    reduce_mod_char
  · have e : 369054083513 - 1 = [2 ^ 3, 17 ^ 1, 643 ^ 1, 4220269 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (369054083513 - 1) / 2 = 184527041756 from by norm_num]
      have h2 : (3 : ZMod 369054083513) ^ 184527041756 = ((369054083512 : ℕ) : ZMod 369054083513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (369054083513 - 1) / 17 = 21709063736 from by norm_num]
      have h2 : (3 : ZMod 369054083513) ^ 21709063736 = ((271010599587 : ℕ) : ZMod 369054083513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (369054083513 - 1) / 643 = 573956584 from by norm_num]
      have h2 : (3 : ZMod 369054083513) ^ 573956584 = ((53075430438 : ℕ) : ZMod 369054083513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (369054083513 - 1) / 4220269 = 87448 from by norm_num]
      have h2 : (3 : ZMod 369054083513) ^ 87448 = ((213836757029 : ℕ) : ZMod 369054083513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_424255915796187428893811 : Nat.Prime 424255915796187428893811 := by
  refine lucas_primality 424255915796187428893811 (7 : ZMod 424255915796187428893811) ?_ (fun q hq hd => ?_)
  · rw [show 424255915796187428893811 - 1 = 424255915796187428893810 from by norm_num]
    reduce_mod_char
  · have e : 424255915796187428893811 - 1 = [2 ^ 1, 5 ^ 1, 13 ^ 1, 269 ^ 1, 32873221 ^ 1, 369054083513 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (424255915796187428893811 - 1) / 2 = 212127957898093714446905 from by norm_num]
      have h2 : (7 : ZMod 424255915796187428893811) ^ 212127957898093714446905 = ((424255915796187428893810 : ℕ) : ZMod 424255915796187428893811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (424255915796187428893811 - 1) / 5 = 84851183159237485778762 from by norm_num]
      have h2 : (7 : ZMod 424255915796187428893811) ^ 84851183159237485778762 = ((567580892332317598252 : ℕ) : ZMod 424255915796187428893811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (424255915796187428893811 - 1) / 13 = 32635070445860571453370 from by norm_num]
      have h2 : (7 : ZMod 424255915796187428893811) ^ 32635070445860571453370 = ((392354055340458269836995 : ℕ) : ZMod 424255915796187428893811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (424255915796187428893811 - 1) / 269 = 1577159538275789698490 from by norm_num]
      have h2 : (7 : ZMod 424255915796187428893811) ^ 1577159538275789698490 = ((424255915796187420505203 : ℕ) : ZMod 424255915796187428893811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (424255915796187428893811 - 1) / 32873221 = 12905821300449610 from by norm_num]
      have h2 : (7 : ZMod 424255915796187428893811) ^ 12905821300449610 = ((269965585924723862185407 : ℕ) : ZMod 424255915796187428893811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_369054083513).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (424255915796187428893811 - 1) / 369054083513 = 1149576538370 from by norm_num]
      have h2 : (7 : ZMod 424255915796187428893811) ^ 1149576538370 = ((178188638043881412347579 : ℕ) : ZMod 424255915796187428893811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_98305423 : Nat.Prime 98305423 := by
  refine lucas_primality 98305423 (6 : ZMod 98305423) ?_ (fun q hq hd => ?_)
  · rw [show 98305423 - 1 = 98305422 from by norm_num]
    reduce_mod_char
  · have e : 98305423 - 1 = [2 ^ 1, 3 ^ 1, 16384237 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (98305423 - 1) / 2 = 49152711 from by norm_num]
      have h2 : (6 : ZMod 98305423) ^ 49152711 = ((98305422 : ℕ) : ZMod 98305423) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (98305423 - 1) / 3 = 32768474 from by norm_num]
      have h2 : (6 : ZMod 98305423) ^ 32768474 = ((57792957 : ℕ) : ZMod 98305423) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (98305423 - 1) / 16384237 = 6 from by norm_num]
      have h2 : (6 : ZMod 98305423) ^ 6 = ((46656 : ℕ) : ZMod 98305423) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1561512307516024940642967698779 : Nat.Prime 1561512307516024940642967698779 := by
  refine lucas_primality 1561512307516024940642967698779 (2 : ZMod 1561512307516024940642967698779) ?_ (fun q hq hd => ?_)
  · rw [show 1561512307516024940642967698779 - 1 = 1561512307516024940642967698778 from by norm_num]
    reduce_mod_char
  · have e : 1561512307516024940642967698779 - 1 = [2 ^ 1, 3 ^ 1, 13 ^ 2, 216493 ^ 1, 2934583 ^ 1, 24656971 ^ 1, 98305423 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1561512307516024940642967698779 - 1) / 2 = 780756153758012470321483849389 from by norm_num]
      have h2 : (2 : ZMod 1561512307516024940642967698779) ^ 780756153758012470321483849389 = ((1561512307516024940642967698778 : ℕ) : ZMod 1561512307516024940642967698779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1561512307516024940642967698779 - 1) / 3 = 520504102505341646880989232926 from by norm_num]
      have h2 : (2 : ZMod 1561512307516024940642967698779) ^ 520504102505341646880989232926 = ((77195363077698461377784589246 : ℕ) : ZMod 1561512307516024940642967698779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1561512307516024940642967698779 - 1) / 13 = 120116331347386533895612899906 from by norm_num]
      have h2 : (2 : ZMod 1561512307516024940642967698779) ^ 120116331347386533895612899906 = ((82764561617419837327109506664 : ℕ) : ZMod 1561512307516024940642967698779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1561512307516024940642967698779 - 1) / 216493 = 7212761186347941691615746 from by norm_num]
      have h2 : (2 : ZMod 1561512307516024940642967698779) ^ 7212761186347941691615746 = ((1293904143060224701584016809660 : ℕ) : ZMod 1561512307516024940642967698779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1561512307516024940642967698779 - 1) / 2934583 = 532107051501363205826166 from by norm_num]
      have h2 : (2 : ZMod 1561512307516024940642967698779) ^ 532107051501363205826166 = ((1134261266033195363774538413907 : ℕ) : ZMod 1561512307516024940642967698779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1561512307516024940642967698779 - 1) / 24656971 = 63329445758606154042318 from by norm_num]
      have h2 : (2 : ZMod 1561512307516024940642967698779) ^ 63329445758606154042318 = ((730830792026865424354198641726 : ℕ) : ZMod 1561512307516024940642967698779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_98305423).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1561512307516024940642967698779 - 1) / 98305423 = 15884294679409750778886 from by norm_num]
      have h2 : (2 : ZMod 1561512307516024940642967698779) ^ 15884294679409750778886 = ((260500292500196168094612965817 : ℕ) : ZMod 1561512307516024940642967698779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_167553393621084508180871720014384259 : Nat.Prime 167553393621084508180871720014384259 := by
  refine lucas_primality 167553393621084508180871720014384259 (2 : ZMod 167553393621084508180871720014384259) ?_ (fun q hq hd => ?_)
  · rw [show 167553393621084508180871720014384259 - 1 = 167553393621084508180871720014384258 from by norm_num]
    reduce_mod_char
  · have e : 167553393621084508180871720014384259 - 1 = [2 ^ 1, 13 ^ 1, 4127 ^ 1, 1561512307516024940642967698779 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (167553393621084508180871720014384259 - 1) / 2 = 83776696810542254090435860007192129 from by norm_num]
      have h2 : (2 : ZMod 167553393621084508180871720014384259) ^ 83776696810542254090435860007192129 = ((167553393621084508180871720014384258 : ℕ) : ZMod 167553393621084508180871720014384259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (167553393621084508180871720014384259 - 1) / 13 = 12888722586237269860067055385721866 from by norm_num]
      have h2 : (2 : ZMod 167553393621084508180871720014384259) ^ 12888722586237269860067055385721866 = ((123083554718360667095679261219813863 : ℕ) : ZMod 167553393621084508180871720014384259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (167553393621084508180871720014384259 - 1) / 4127 = 40599319995416648456717160168254 from by norm_num]
      have h2 : (2 : ZMod 167553393621084508180871720014384259) ^ 40599319995416648456717160168254 = ((28886158607099207013456947652306774 : ℕ) : ZMod 167553393621084508180871720014384259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1561512307516024940642967698779).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (167553393621084508180871720014384259 - 1) / 1561512307516024940642967698779 = 107302 from by norm_num]
      have h2 : (2 : ZMod 167553393621084508180871720014384259) ^ 107302 = ((14029442537869252047317686383472478 : ℕ) : ZMod 167553393621084508180871720014384259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1453023029482044854944519555964740294049 : Nat.Prime 1453023029482044854944519555964740294049 := by
  refine lucas_primality 1453023029482044854944519555964740294049 (3 : ZMod 1453023029482044854944519555964740294049) ?_ (fun q hq hd => ?_)
  · rw [show 1453023029482044854944519555964740294049 - 1 = 1453023029482044854944519555964740294048 from by norm_num]
    reduce_mod_char
  · have e : 1453023029482044854944519555964740294049 - 1 = [2 ^ 5, 271 ^ 1, 167553393621084508180871720014384259 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1453023029482044854944519555964740294049 - 1) / 2 = 726511514741022427472259777982370147024 from by norm_num]
      have h2 : (3 : ZMod 1453023029482044854944519555964740294049) ^ 726511514741022427472259777982370147024 = ((1453023029482044854944519555964740294048 : ℕ) : ZMod 1453023029482044854944519555964740294049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1453023029482044854944519555964740294049 - 1) / 271 = 5361708595874704261787895040460296288 from by norm_num]
      have h2 : (3 : ZMod 1453023029482044854944519555964740294049) ^ 5361708595874704261787895040460296288 = ((948945803426304028534742878037549849784 : ℕ) : ZMod 1453023029482044854944519555964740294049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_167553393621084508180871720014384259).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1453023029482044854944519555964740294049 - 1) / 167553393621084508180871720014384259 = 8672 from by norm_num]
      have h2 : (3 : ZMod 1453023029482044854944519555964740294049) ^ 8672 = ((304595914781450497117367231531761362125 : ℕ) : ZMod 1453023029482044854944519555964740294049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_406072181461 : Nat.Prime 406072181461 := by
  refine lucas_primality 406072181461 (2 : ZMod 406072181461) ?_ (fun q hq hd => ?_)
  · rw [show 406072181461 - 1 = 406072181460 from by norm_num]
    reduce_mod_char
  · have e : 406072181461 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 11 ^ 1, 4871 ^ 1, 126311 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (406072181461 - 1) / 2 = 203036090730 from by norm_num]
      have h2 : (2 : ZMod 406072181461) ^ 203036090730 = ((406072181460 : ℕ) : ZMod 406072181461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (406072181461 - 1) / 3 = 135357393820 from by norm_num]
      have h2 : (2 : ZMod 406072181461) ^ 135357393820 = ((364481738657 : ℕ) : ZMod 406072181461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (406072181461 - 1) / 5 = 81214436292 from by norm_num]
      have h2 : (2 : ZMod 406072181461) ^ 81214436292 = ((251836524402 : ℕ) : ZMod 406072181461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (406072181461 - 1) / 11 = 36915652860 from by norm_num]
      have h2 : (2 : ZMod 406072181461) ^ 36915652860 = ((403582939166 : ℕ) : ZMod 406072181461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (406072181461 - 1) / 4871 = 83365260 from by norm_num]
      have h2 : (2 : ZMod 406072181461) ^ 83365260 = ((132137650264 : ℕ) : ZMod 406072181461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (406072181461 - 1) / 126311 = 3214860 from by norm_num]
      have h2 : (2 : ZMod 406072181461) ^ 3214860 = ((166251512051 : ℕ) : ZMod 406072181461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_42007034230754173811 : Nat.Prime 42007034230754173811 := by
  refine lucas_primality 42007034230754173811 (2 : ZMod 42007034230754173811) ?_ (fun q hq hd => ?_)
  · rw [show 42007034230754173811 - 1 = 42007034230754173810 from by norm_num]
    reduce_mod_char
  · have e : 42007034230754173811 - 1 = [2 ^ 1, 5 ^ 1, 17 ^ 1, 19 ^ 1, 32027 ^ 1, 406072181461 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42007034230754173811 - 1) / 2 = 21003517115377086905 from by norm_num]
      have h2 : (2 : ZMod 42007034230754173811) ^ 21003517115377086905 = ((42007034230754173810 : ℕ) : ZMod 42007034230754173811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42007034230754173811 - 1) / 5 = 8401406846150834762 from by norm_num]
      have h2 : (2 : ZMod 42007034230754173811) ^ 8401406846150834762 = ((34957540836634055095 : ℕ) : ZMod 42007034230754173811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42007034230754173811 - 1) / 17 = 2471002013573774930 from by norm_num]
      have h2 : (2 : ZMod 42007034230754173811) ^ 2471002013573774930 = ((31404500640903788347 : ℕ) : ZMod 42007034230754173811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42007034230754173811 - 1) / 19 = 2210896538460745990 from by norm_num]
      have h2 : (2 : ZMod 42007034230754173811) ^ 2210896538460745990 = ((8974776169980849766 : ℕ) : ZMod 42007034230754173811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42007034230754173811 - 1) / 32027 = 1311613146119030 from by norm_num]
      have h2 : (2 : ZMod 42007034230754173811) ^ 1311613146119030 = ((35340654168517942190 : ℕ) : ZMod 42007034230754173811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_406072181461).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42007034230754173811 - 1) / 406072181461 = 103447210 from by norm_num]
      have h2 : (2 : ZMod 42007034230754173811) ^ 103447210 = ((8152609439335070732 : ℕ) : ZMod 42007034230754173811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1393915463 : Nat.Prime 1393915463 := by
  refine lucas_primality 1393915463 (5 : ZMod 1393915463) ?_ (fun q hq hd => ?_)
  · rw [show 1393915463 - 1 = 1393915462 from by norm_num]
    reduce_mod_char
  · have e : 1393915463 - 1 = [2 ^ 1, 2063 ^ 1, 337837 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1393915463 - 1) / 2 = 696957731 from by norm_num]
      have h2 : (5 : ZMod 1393915463) ^ 696957731 = ((1393915462 : ℕ) : ZMod 1393915463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1393915463 - 1) / 2063 = 675674 from by norm_num]
      have h2 : (5 : ZMod 1393915463) ^ 675674 = ((364374100 : ℕ) : ZMod 1393915463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1393915463 - 1) / 337837 = 4126 from by norm_num]
      have h2 : (5 : ZMod 1393915463) ^ 4126 = ((1285207032 : ℕ) : ZMod 1393915463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1262887409479 : Nat.Prime 1262887409479 := by
  refine lucas_primality 1262887409479 (6 : ZMod 1262887409479) ?_ (fun q hq hd => ?_)
  · rw [show 1262887409479 - 1 = 1262887409478 from by norm_num]
    reduce_mod_char
  · have e : 1262887409479 - 1 = [2 ^ 1, 3 ^ 1, 151 ^ 1, 1393915463 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1262887409479 - 1) / 2 = 631443704739 from by norm_num]
      have h2 : (6 : ZMod 1262887409479) ^ 631443704739 = ((1262887409478 : ℕ) : ZMod 1262887409479) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1262887409479 - 1) / 3 = 420962469826 from by norm_num]
      have h2 : (6 : ZMod 1262887409479) ^ 420962469826 = ((465814188270 : ℕ) : ZMod 1262887409479) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1262887409479 - 1) / 151 = 8363492778 from by norm_num]
      have h2 : (6 : ZMod 1262887409479) ^ 8363492778 = ((487857539251 : ℕ) : ZMod 1262887409479) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1393915463).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1262887409479 - 1) / 1393915463 = 906 from by norm_num]
      have h2 : (6 : ZMod 1262887409479) ^ 906 = ((638622238309 : ℕ) : ZMod 1262887409479) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_810861401403659 : Nat.Prime 810861401403659 := by
  refine lucas_primality 810861401403659 (2 : ZMod 810861401403659) ?_ (fun q hq hd => ?_)
  · rw [show 810861401403659 - 1 = 810861401403658 from by norm_num]
    reduce_mod_char
  · have e : 810861401403659 - 1 = [2 ^ 1, 11 ^ 2, 31 ^ 1, 67 ^ 1, 4441 ^ 1, 363257 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (810861401403659 - 1) / 2 = 405430700701829 from by norm_num]
      have h2 : (2 : ZMod 810861401403659) ^ 405430700701829 = ((810861401403658 : ℕ) : ZMod 810861401403659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (810861401403659 - 1) / 11 = 73714672854878 from by norm_num]
      have h2 : (2 : ZMod 810861401403659) ^ 73714672854878 = ((267159686903072 : ℕ) : ZMod 810861401403659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (810861401403659 - 1) / 31 = 26156819400118 from by norm_num]
      have h2 : (2 : ZMod 810861401403659) ^ 26156819400118 = ((388932402699762 : ℕ) : ZMod 810861401403659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (810861401403659 - 1) / 67 = 12102408976174 from by norm_num]
      have h2 : (2 : ZMod 810861401403659) ^ 12102408976174 = ((111005928382725 : ℕ) : ZMod 810861401403659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (810861401403659 - 1) / 4441 = 182585318938 from by norm_num]
      have h2 : (2 : ZMod 810861401403659) ^ 182585318938 = ((807004057353110 : ℕ) : ZMod 810861401403659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (810861401403659 - 1) / 363257 = 2232197594 from by norm_num]
      have h2 : (2 : ZMod 810861401403659) ^ 2232197594 = ((566098549015185 : ℕ) : ZMod 810861401403659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1292321638187455252994177180183 : Nat.Prime 1292321638187455252994177180183 := by
  refine lucas_primality 1292321638187455252994177180183 (5 : ZMod 1292321638187455252994177180183) ?_ (fun q hq hd => ?_)
  · rw [show 1292321638187455252994177180183 - 1 = 1292321638187455252994177180182 from by norm_num]
    reduce_mod_char
  · have e : 1292321638187455252994177180183 - 1 = [2 ^ 1, 631 ^ 1, 1262887409479 ^ 1, 810861401403659 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1292321638187455252994177180183 - 1) / 2 = 646160819093727626497088590091 from by norm_num]
      have h2 : (5 : ZMod 1292321638187455252994177180183) ^ 646160819093727626497088590091 = ((1292321638187455252994177180182 : ℕ) : ZMod 1292321638187455252994177180183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1292321638187455252994177180183 - 1) / 631 = 2048053309330356977803767322 from by norm_num]
      have h2 : (5 : ZMod 1292321638187455252994177180183) ^ 2048053309330356977803767322 = ((88629181910741065120678539556 : ℕ) : ZMod 1292321638187455252994177180183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1262887409479).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1292321638187455252994177180183 - 1) / 1262887409479 = 1023307088571417658 from by norm_num]
      have h2 : (5 : ZMod 1292321638187455252994177180183) ^ 1023307088571417658 = ((1256727774195954641712687077614 : ℕ) : ZMod 1292321638187455252994177180183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_810861401403659).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1292321638187455252994177180183 - 1) / 810861401403659 = 1593763910762498 from by norm_num]
      have h2 : (5 : ZMod 1292321638187455252994177180183) ^ 1593763910762498 = ((73577415758099977372433517637 : ℕ) : ZMod 1292321638187455252994177180183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_441710011 : Nat.Prime 441710011 := by
  refine lucas_primality 441710011 (2 : ZMod 441710011) ?_ (fun q hq hd => ?_)
  · rw [show 441710011 - 1 = 441710010 from by norm_num]
    reduce_mod_char
  · have e : 441710011 - 1 = [2 ^ 1, 3 ^ 4, 5 ^ 1, 7 ^ 2, 31 ^ 1, 359 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (441710011 - 1) / 2 = 220855005 from by norm_num]
      have h2 : (2 : ZMod 441710011) ^ 220855005 = ((441710010 : ℕ) : ZMod 441710011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (441710011 - 1) / 3 = 147236670 from by norm_num]
      have h2 : (2 : ZMod 441710011) ^ 147236670 = ((172899517 : ℕ) : ZMod 441710011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (441710011 - 1) / 5 = 88342002 from by norm_num]
      have h2 : (2 : ZMod 441710011) ^ 88342002 = ((150462980 : ℕ) : ZMod 441710011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (441710011 - 1) / 7 = 63101430 from by norm_num]
      have h2 : (2 : ZMod 441710011) ^ 63101430 = ((195718097 : ℕ) : ZMod 441710011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (441710011 - 1) / 31 = 14248710 from by norm_num]
      have h2 : (2 : ZMod 441710011) ^ 14248710 = ((307933481 : ℕ) : ZMod 441710011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (441710011 - 1) / 359 = 1230390 from by norm_num]
      have h2 : (2 : ZMod 441710011) ^ 1230390 = ((231368839 : ℕ) : ZMod 441710011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_17670495028872163 : Nat.Prime 17670495028872163 := by
  refine lucas_primality 17670495028872163 (2 : ZMod 17670495028872163) ?_ (fun q hq hd => ?_)
  · rw [show 17670495028872163 - 1 = 17670495028872162 from by norm_num]
    reduce_mod_char
  · have e : 17670495028872163 - 1 = [2 ^ 1, 3 ^ 1, 6667457 ^ 1, 441710011 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17670495028872163 - 1) / 2 = 8835247514436081 from by norm_num]
      have h2 : (2 : ZMod 17670495028872163) ^ 8835247514436081 = ((17670495028872162 : ℕ) : ZMod 17670495028872163) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17670495028872163 - 1) / 3 = 5890165009624054 from by norm_num]
      have h2 : (2 : ZMod 17670495028872163) ^ 5890165009624054 = ((1486204505973910 : ℕ) : ZMod 17670495028872163) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17670495028872163 - 1) / 6667457 = 2650260066 from by norm_num]
      have h2 : (2 : ZMod 17670495028872163) ^ 2650260066 = ((16748007769422588 : ℕ) : ZMod 17670495028872163) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_441710011).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17670495028872163 - 1) / 441710011 = 40004742 from by norm_num]
      have h2 : (2 : ZMod 17670495028872163) ^ 40004742 = ((10612626572554881 : ℕ) : ZMod 17670495028872163) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_516319099 : Nat.Prime 516319099 := by
  refine lucas_primality 516319099 (2 : ZMod 516319099) ?_ (fun q hq hd => ?_)
  · rw [show 516319099 - 1 = 516319098 from by norm_num]
    reduce_mod_char
  · have e : 516319099 - 1 = [2 ^ 1, 3 ^ 1, 977 ^ 1, 88079 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (516319099 - 1) / 2 = 258159549 from by norm_num]
      have h2 : (2 : ZMod 516319099) ^ 258159549 = ((516319098 : ℕ) : ZMod 516319099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (516319099 - 1) / 3 = 172106366 from by norm_num]
      have h2 : (2 : ZMod 516319099) ^ 172106366 = ((434257092 : ℕ) : ZMod 516319099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (516319099 - 1) / 977 = 528474 from by norm_num]
      have h2 : (2 : ZMod 516319099) ^ 528474 = ((316428959 : ℕ) : ZMod 516319099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (516319099 - 1) / 88079 = 5862 from by norm_num]
      have h2 : (2 : ZMod 516319099) ^ 5862 = ((42154709 : ℕ) : ZMod 516319099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 : Nat.Prime 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 := by
  refine lucas_primality 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 (7 : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) ?_ (fun q hq hd => ?_)
  · rw [show 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 - 1 = 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368248 from by norm_num]
    reduce_mod_char
  · have e : 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 - 1 = [2 ^ 3, 3 ^ 1, 311 ^ 1, 39439 ^ 1, 148873 ^ 1, 516319099 ^ 1, 17670495028872163 ^ 1, 42007034230754173811 ^ 1, 1292321638187455252994177180183 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 - 1) / 2 = 10852830317045768504528532031213173900847048845291745207628512963714478337561494410184124 from by norm_num]
      have h2 : (7 : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) ^ 10852830317045768504528532031213173900847048845291745207628512963714478337561494410184124 = ((21705660634091537009057064062426347801694097690583490415257025927428956675122988820368248 : ℕ) : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 - 1) / 3 = 7235220211363845669685688020808782600564699230194496805085675309142985558374329606789416 from by norm_num]
      have h2 : (7 : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) ^ 7235220211363845669685688020808782600564699230194496805085675309142985558374329606789416 = ((2606151293375680710041833746391414083513450786966456762079937789909643603112651542040836 : ℕ) : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 - 1) / 311 = 69793121009940633469636861937062211581009960419882605836839311663758703135443693956168 from by norm_num]
      have h2 : (7 : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) ^ 69793121009940633469636861937062211581009960419882605836839311663758703135443693956168 = ((21705660634091537009057064062426347801694097690583490415257025927277840947671160173529977 : ℕ) : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 - 1) / 39439 = 550360319330904358859430108837099008638507510093650711611780874956995782730875245832 from by norm_num]
      have h2 : (7 : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) ^ 550360319330904358859430108837099008638507510093650711611780874956995782730875245832 = ((21382580662692369085482166331232043975815099824636373250034849001093498203050261837234182 : ℕ) : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 - 1) / 148873 = 145799847078325398218999174211753291743258332206535036005568678856669487920059304376 from by norm_num]
      have h2 : (7 : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) ^ 145799847078325398218999174211753291743258332206535036005568678856669487920059304376 = ((20623150417320089679013273105430618803224207037985932232910711457753484873857840894096891 : ℕ) : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_516319099).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 - 1) / 516319099 = 42039236348472821085894140170914630066191097243496488235189273770074030662814952 from by norm_num]
      have h2 : (7 : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) ^ 42039236348472821085894140170914630066191097243496488235189273770074030662814952 = ((3533944345290980610704843673807538668864977819985913055505138889515641724071263251134411 : ℕ) : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_17670495028872163).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 - 1) / 17670495028872163 = 1228356115582853735444427052412282310305237042054232594131028453349216296 from by norm_num]
      have h2 : (7 : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) ^ 1228356115582853735444427052412282310305237042054232594131028453349216296 = ((12916591694046433037896189625277765820537727735526366595642568871382940359883793830250334 : ℕ) : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_42007034230754173811).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 - 1) / 42007034230754173811 = 516714903386357065397846306109206077646568603298905538103115525888168 from by norm_num]
      have h2 : (7 : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) ^ 516714903386357065397846306109206077646568603298905538103115525888168 = ((18925313173589891631817681173424179636007720198829734022273115833715412433524869044135159 : ℕ) : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1292321638187455252994177180183).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 - 1) / 1292321638187455252994177180183 = 16795865667416042879191793883513464555483136139981251466056 from by norm_num]
      have h2 : (7 : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) ^ 16795865667416042879191793883513464555483136139981251466056 = ((15203559518314295132845358205298825033324607103632905258488621701548686501836083313279037 : ℕ) : ZMod 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_308761441 : Nat.Prime 308761441 := by
  refine lucas_primality 308761441 (17 : ZMod 308761441) ?_ (fun q hq hd => ?_)
  · rw [show 308761441 - 1 = 308761440 from by norm_num]
    reduce_mod_char
  · have e : 308761441 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 13 ^ 1, 49481 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308761441 - 1) / 2 = 154380720 from by norm_num]
      have h2 : (17 : ZMod 308761441) ^ 154380720 = ((308761440 : ℕ) : ZMod 308761441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308761441 - 1) / 3 = 102920480 from by norm_num]
      have h2 : (17 : ZMod 308761441) ^ 102920480 = ((282204286 : ℕ) : ZMod 308761441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308761441 - 1) / 5 = 61752288 from by norm_num]
      have h2 : (17 : ZMod 308761441) ^ 61752288 = ((35908262 : ℕ) : ZMod 308761441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308761441 - 1) / 13 = 23750880 from by norm_num]
      have h2 : (17 : ZMod 308761441) ^ 23750880 = ((308761425 : ℕ) : ZMod 308761441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308761441 - 1) / 49481 = 6240 from by norm_num]
      have h2 : (17 : ZMod 308761441) ^ 6240 = ((241085963 : ℕ) : ZMod 308761441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_84159375948762099254554456081 : Nat.Prime 84159375948762099254554456081 := by
  refine lucas_primality 84159375948762099254554456081 (83 : ZMod 84159375948762099254554456081) ?_ (fun q hq hd => ?_)
  · rw [show 84159375948762099254554456081 - 1 = 84159375948762099254554456080 from by norm_num]
    reduce_mod_char
  · have e : 84159375948762099254554456081 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 1, 97 ^ 1, 257 ^ 1, 421 ^ 1, 673 ^ 1, 859 ^ 1, 90841 ^ 1, 137089 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 2 = 42079687974381049627277228040 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 42079687974381049627277228040 = ((84159375948762099254554456080 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 3 = 28053125316254033084851485360 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 28053125316254033084851485360 = ((4503599627370495 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 5 = 16831875189752419850910891216 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 16831875189752419850910891216 = ((11435863083980520899450414520 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 7 = 12022767992680299893507779440 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 12022767992680299893507779440 = ((74662600791481927477124672443 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 13 = 6473798149904776865734958160 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 6473798149904776865734958160 = ((4722366482869645213696 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 17 = 4950551526397770544385556240 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 4950551526397770544385556240 = ((39348875729423789757659641382 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 97 = 867622432461464940768602640 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 867622432461464940768602640 = ((21918906206941868732369675763 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 257 = 327468388905689102157799440 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 327468388905689102157799440 = ((10704966249718233285857030436 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 421 = 199903505816537052861174480 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 199903505816537052861174480 = ((59121302119014873351613202389 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 673 = 125051078675723773037970960 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 125051078675723773037970960 = ((63661248640154215113310086442 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 859 = 97973662338489056175267120 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 97973662338489056175267120 = ((79124199601514526835032928488 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 90841 = 926447044272543226676880 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 926447044272543226676880 = ((68725869389557593960862862298 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 137089 = 613903201196026663368720 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 613903201196026663368720 = ((66527993628709433932574257657 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 : Nat.Prime 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 := by
  refine lucas_primality 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ?_ (fun q hq hd => ?_)
  · rw [show 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1 = 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434730 from by norm_num]
    reduce_mod_char
  · have e : 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 7 ^ 1, 13 ^ 2, 17 ^ 1, 53 ^ 1, 79 ^ 1, 157 ^ 1, 241 ^ 1, 313 ^ 1, 1249 ^ 1, 1613 ^ 1, 2731 ^ 1, 3121 ^ 1, 8191 ^ 1, 21841 ^ 1, 121369 ^ 1, 858001 ^ 1, 22366891 ^ 1, 308761441 ^ 1, 84159375948762099254554456081 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 2 = 2781233119688685003118517846574937649222271513485224960868543760185181934610209049509065217365 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 2781233119688685003118517846574937649222271513485224960868543760185181934610209049509065217365 = ((5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434730 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 3 = 1854155413125790002079011897716625099481514342323483307245695840123454623073472699672710144910 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 1854155413125790002079011897716625099481514342323483307245695840123454623073472699672710144910 = ((1148504657410833284440608587668779155666248184225405704863726330908455569217291479709947850692 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 5 = 1112493247875474001247407138629975059688908605394089984347417504074072773844083619803626086946 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 1112493247875474001247407138629975059688908605394089984347417504074072773844083619803626086946 = ((64134290553828539322300395429908966854750532514834125250991538572967316465076832271021204106 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 7 = 794638034196767143748147956164267899777791860995778560248155360052909124174345442716875776390 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 794638034196767143748147956164267899777791860995778560248155360052909124174345442716875776390 = ((2523612606383337294930810904675955568317097786481482904749163998845605618482740172620478432246 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 13 = 427882018413643846633618130242298099880349463613111532441314424643874143786186007616779264210 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 427882018413643846633618130242298099880349463613111532441314424643874143786186007616779264210 = ((1964497429657288840644871349015733497987862001485101820861049101150487282201370435953963809517 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 17 = 327203896433962941543355040773522076379090766292379407161005148257080227601201064648125319690 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 327203896433962941543355040773522076379090766292379407161005148257080227601201064648125319690 = ((662509048925326108742283503172463961772887096079463558144217012109036755498925020034383555862 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 53 = 104952193195799434079944069682073118838576283527744338145982783403214412626800341490908121410 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 104952193195799434079944069682073118838576283527744338145982783403214412626800341490908121410 = ((807124117453346232919122871885059055055777664772752405048564378809476404981695731033954440126 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 79 = 70410965055409746914392856875314877195500544645195568629583386333802074293929343025545954870 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 70410965055409746914392856875314877195500544645195568629583386333802074293929343025545954870 = ((4942426453298087275995734738762103249677305014680653006648719635346430683396253860344988299235 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 157 = 35429721269919554179853730529617040117481165776881846635268073378155183880384828656166435890 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 35429721269919554179853730529617040117481165776881846635268073378155183880384828656166435890 = ((5118746375564093776493183768967647026358798417168845965800946080778421954823710739948674340839 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 241 = 23080772777499460606792679224688279246657854883694812953265923321038854229130365556091827530 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 23080772777499460606792679224688279246657854883694812953265923321038854229130365556091827530 = ((1190289953441627444766027962273950824114996786959264696222528604119478894653846822357151414920 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 313 = 17771457633793514396923436719328675074902693376902395916092931374985188080576415651815113210 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 17771457633793514396923436719328675074902693376902395916092931374985188080576415651815113210 = ((5562466239377370006237035693149875298444543026970449921737087520370363869219841638265827011243 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 1249 = 4453535820158022422927970931264912168490426762986749336859157342170027117069990471591777770 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 4453535820158022422927970931264912168490426762986749336859157342170027117069990471591777770 = ((1240246910053325187569073588705511250097474499074471688950411692796605522043238780203692333326 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 1613 = 3448522157084544331207089704370660445408892143193087366235020161419940402492509670810992210 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 3448522157084544331207089704370660445408892143193087366235020161419940402492509670810992210 = ((1752915670359520218124682744265679413251468294908754357228809853101247220183812265021322015006 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 2731 = 2036787345066777739376431963804421566621949112768381516564294222032355865697699779940728830 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 2036787345066777739376431963804421566621949112768381516564294222032355865697699779940728830 = ((364578046764427133811116089391640525672155862137977927795022696736924764242266802901980247823 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 3121 = 1782270502844399233014109481944849502865922148981239962107365434274387654348099358865149130 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 1782270502844399233014109481944849502865922148981239962107365434274387654348099358865149130 = ((1959121451270987998626504546907139138797261668605801021124960942376432891314256784910963622205 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 8191 = 679094889436866073280067841917943510980898916734275414691379260208810141523674532904179030 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 679094889436866073280067841917943510980898916734275414691379260208810141523674532904179030 = ((4899418649307493505685239241355456611554468578147396250593043907496998442512956526378681639114 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 21841 = 254680016454254384242344017817401918339111900873149119625341674848695749701040158372699530 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 254680016454254384242344017817401918339111900873149119625341674848695749701040158372699530 = ((260584756137046828058080426314459465124248848232284802396987498225481043865867099429088689314 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 121369 = 45831029664719739029216980391614623985074796916596906308341401184572369132318945521658170 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 45831029664719739029216980391614623985074796916596906308341401184572369132318945521658170 = ((3128795496370520344992407813013770333363989257365549840894728419796942140074601972085631235633 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 858001 = 6483053329048998784659966239141767082374662764927371788304544540589537622007920852094730 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 6483053329048998784659966239141767082374662764927371788304544540589537622007920852094730 = ((1917588924765716630815125116354718840833852817288658825307571276113488896612225349488460600483 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 22366891 = 248691972405881980031871022805533200767354883026454142497367538491172683285326427308030 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 248691972405881980031871022805533200767354883026454142497367538491172683285326427308030 = ((525002842868030329039464996228210703213682624362731244788674565290945043926129844058957394125 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_308761441).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 308761441 = 18015417408864113981891397161700237363656244326733952254540383235128002493097634231530 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 18015417408864113981891397161700237363656244326733952254540383235128002493097634231530 = ((3694600170349377137466168278447248975685304982674608247806615879735738514191222276019948895194 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_84159375948762099254554456081).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 84159375948762099254554456081 = 66094433052401790702470203697203715578808419128233868549360888330 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 66094433052401790702470203697203715578808419128233868549360888330 = ((703138134328676702400538470149617951556345484969042910801983515034314942029246730771554676983 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_179299534877 : Nat.Prime 179299534877 := by
  refine lucas_primality 179299534877 (2 : ZMod 179299534877) ?_ (fun q hq hd => ?_)
  · rw [show 179299534877 - 1 = 179299534876 from by norm_num]
    reduce_mod_char
  · have e : 179299534877 - 1 = [2 ^ 2, 7 ^ 1, 11 ^ 1, 53 ^ 1, 73 ^ 1, 379 ^ 1, 397 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 2 = 89649767438 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 89649767438 = ((179299534876 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 7 = 25614219268 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 25614219268 = ((97433609777 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 11 = 16299957716 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 16299957716 = ((143566895690 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 53 = 3383010092 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 3383010092 = ((154769305081 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 73 = 2456158012 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 2456158012 = ((67327353113 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 379 = 473085844 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 473085844 = ((102841375754 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 397 = 451636108 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 451636108 = ((31482535414 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_155285743288572277679887 : Nat.Prime 155285743288572277679887 := by
  refine lucas_primality 155285743288572277679887 (7 : ZMod 155285743288572277679887) ?_ (fun q hq hd => ?_)
  · rw [show 155285743288572277679887 - 1 = 155285743288572277679886 from by norm_num]
    reduce_mod_char
  · have e : 155285743288572277679887 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 37 ^ 2, 83 ^ 1, 173 ^ 1, 1049 ^ 1, 179299534877 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 2 = 77642871644286138839943 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 77642871644286138839943 = ((155285743288572277679886 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 3 = 51761914429524092559962 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 51761914429524092559962 = ((45173811239863550073009 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 7 = 22183677612653182525698 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 22183677612653182525698 = ((145819477496274857736139 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 37 = 4196911980772223721078 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 4196911980772223721078 = ((136566097260737592495614 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 83 = 1870912569741834670842 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 1870912569741834670842 = ((120156020248387100991375 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 173 = 897605452535099870982 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 897605452535099870982 = ((64 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 1049 = 148032167100640874814 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 148032167100640874814 = ((139924100744100887877009 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_179299534877).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 179299534877 = 866068857318 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 866068857318 = ((75604042182166458491079 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_28046273581 : Nat.Prime 28046273581 := by
  refine lucas_primality 28046273581 (2 : ZMod 28046273581) ?_ (fun q hq hd => ?_)
  · rw [show 28046273581 - 1 = 28046273580 from by norm_num]
    reduce_mod_char
  · have e : 28046273581 - 1 = [2 ^ 2, 3 ^ 2, 5 ^ 1, 13 ^ 1, 307 ^ 1, 39041 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28046273581 - 1) / 2 = 14023136790 from by norm_num]
      have h2 : (2 : ZMod 28046273581) ^ 14023136790 = ((28046273580 : ℕ) : ZMod 28046273581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28046273581 - 1) / 3 = 9348757860 from by norm_num]
      have h2 : (2 : ZMod 28046273581) ^ 9348757860 = ((22251013166 : ℕ) : ZMod 28046273581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28046273581 - 1) / 5 = 5609254716 from by norm_num]
      have h2 : (2 : ZMod 28046273581) ^ 5609254716 = ((22358905908 : ℕ) : ZMod 28046273581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28046273581 - 1) / 13 = 2157405660 from by norm_num]
      have h2 : (2 : ZMod 28046273581) ^ 2157405660 = ((6871355745 : ℕ) : ZMod 28046273581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28046273581 - 1) / 307 = 91355940 from by norm_num]
      have h2 : (2 : ZMod 28046273581) ^ 91355940 = ((8310140850 : ℕ) : ZMod 28046273581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28046273581 - 1) / 39041 = 718380 from by norm_num]
      have h2 : (2 : ZMod 28046273581) ^ 718380 = ((18298241638 : ℕ) : ZMod 28046273581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1643464247728189221623609 : Nat.Prime 1643464247728189221623609 := by
  refine lucas_primality 1643464247728189221623609 (3 : ZMod 1643464247728189221623609) ?_ (fun q hq hd => ?_)
  · rw [show 1643464247728189221623609 - 1 = 1643464247728189221623608 from by norm_num]
    reduce_mod_char
  · have e : 1643464247728189221623609 - 1 = [2 ^ 3, 17 ^ 1, 173 ^ 1, 22541 ^ 1, 110491 ^ 1, 28046273581 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1643464247728189221623609 - 1) / 2 = 821732123864094610811804 from by norm_num]
      have h2 : (3 : ZMod 1643464247728189221623609) ^ 821732123864094610811804 = ((1643464247728189221623608 : ℕ) : ZMod 1643464247728189221623609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1643464247728189221623609 - 1) / 17 = 96674367513422895389624 from by norm_num]
      have h2 : (3 : ZMod 1643464247728189221623609) ^ 96674367513422895389624 = ((291555683615566311676479 : ℕ) : ZMod 1643464247728189221623609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1643464247728189221623609 - 1) / 173 = 9499793339469301859096 from by norm_num]
      have h2 : (3 : ZMod 1643464247728189221623609) ^ 9499793339469301859096 = ((4194304 : ℕ) : ZMod 1643464247728189221623609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1643464247728189221623609 - 1) / 22541 = 72909997237398040088 from by norm_num]
      have h2 : (3 : ZMod 1643464247728189221623609) ^ 72909997237398040088 = ((714575637068173386075171 : ℕ) : ZMod 1643464247728189221623609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1643464247728189221623609 - 1) / 110491 = 14874191090027144488 from by norm_num]
      have h2 : (3 : ZMod 1643464247728189221623609) ^ 14874191090027144488 = ((178427696342233853775396 : ℕ) : ZMod 1643464247728189221623609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_28046273581).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1643464247728189221623609 - 1) / 28046273581 = 58598310502168 from by norm_num]
      have h2 : (3 : ZMod 1643464247728189221623609) ^ 58598310502168 = ((1058537451063726728928090 : ℕ) : ZMod 1643464247728189221623609) := by
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

theorem prime_70084436712553223 : Nat.Prime 70084436712553223 := by
  refine lucas_primality 70084436712553223 (5 : ZMod 70084436712553223) ?_ (fun q hq hd => ?_)
  · rw [show 70084436712553223 - 1 = 70084436712553222 from by norm_num]
    reduce_mod_char
  · have e : 70084436712553223 - 1 = [2 ^ 1, 173 ^ 1, 3181 ^ 1, 37987 ^ 1, 1676281 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70084436712553223 - 1) / 2 = 35042218356276611 from by norm_num]
      have h2 : (5 : ZMod 70084436712553223) ^ 35042218356276611 = ((70084436712553222 : ℕ) : ZMod 70084436712553223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70084436712553223 - 1) / 173 = 405112350939614 from by norm_num]
      have h2 : (5 : ZMod 70084436712553223) ^ 405112350939614 = ((4503599627370496 : ℕ) : ZMod 70084436712553223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70084436712553223 - 1) / 3181 = 22032202676062 from by norm_num]
      have h2 : (5 : ZMod 70084436712553223) ^ 22032202676062 = ((25063569565806733 : ℕ) : ZMod 70084436712553223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70084436712553223 - 1) / 37987 = 1844958451906 from by norm_num]
      have h2 : (5 : ZMod 70084436712553223) ^ 1844958451906 = ((54191323626226478 : ℕ) : ZMod 70084436712553223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70084436712553223 - 1) / 1676281 = 41809479862 from by norm_num]
      have h2 : (5 : ZMod 70084436712553223) ^ 41809479862 = ((64078222363299230 : ℕ) : ZMod 70084436712553223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 : Nat.Prime 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 := by
  refine lucas_primality 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ?_ (fun q hq hd => ?_)
  · rw [show 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1 = 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606442 from by norm_num]
    reduce_mod_char
  · have e : 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1 = [2 ^ 1, 347 ^ 1, 4153 ^ 1, 730753 ^ 1, 1505447 ^ 1, 35374479827 ^ 1, 47635010587 ^ 1, 70084436712553223 ^ 1, 155285743288572277679887 ^ 1, 1643464247728189221623609 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 2 = 47781221166459823158558768652126811266595103941005856744533100820560893251843433501458719856460951803221 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 47781221166459823158558768652126811266595103941005856744533100820560893251843433501458719856460951803221 = ((95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606442 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 347 = 275396087414754023968638436035313033236859388708967474031891071011878347272872815570367261420524217886 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 275396087414754023968638436035313033236859388708967474031891071011878347272872815570367261420524217886 = ((295147905179352825856 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 4153 = 23010460470243112525190834891464874195326320222011007341455863626564359861229681435809641154086661114 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 23010460470243112525190834891464874195326320222011007341455863626564359861229681435809641154086661114 = ((74797293787698466550751863501757396910657567963487480625152498631695589161160249376584218422897450991778 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 730753 = 130772562456698291101257931618828280599860976119169833704502344350446438815423086874658659920550314 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 130772562456698291101257931618828280599860976119169833704502344350446438815423086874658659920550314 = ((32541282119383636475833603355699798712820715194565271724134958738894487231181265573558099891549724164134 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 1505447 = 63477785888788941966816193000652711475854153538458486741191288461913163667460141076316495840054086 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 63477785888788941966816193000652711475854153538458486741191288461913163667460141076316495840054086 = ((28613855188095900229276816659869554853989989587960776396589459205384840468455481894703443201519013052741 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_35374479827).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 35374479827 = 2701451520991142751740385536560263793506387773293538117559559772438368765718242740873461147246 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 2701451520991142751740385536560263793506387773293538117559559772438368765718242740873461147246 = ((5787781112995194852964444892620204404624229725688165730830993319458933250484764351772718054285457720119 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_47635010587).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 47635010587 = 2006138786479024118057923783457846689723256088630198449903541776263776659999650836288738027166 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 2006138786479024118057923783457846689723256088630198449903541776263776659999650836288738027166 = ((13852109047059171500480485738715756626307602158531106897892820855629330643549769120255469894161377114972 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_70084436712553223).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 70084436712553223 = 1363533001269066524213465815356508195351495719511673329015865732696018849832538515198854 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 1363533001269066524213465815356508195351495719511673329015865732696018849832538515198854 = ((62931673970413538746766529349926070678504744039875963370370673208247039552507785073889486433836373666996 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_155285743288572277679887).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 155285743288572277679887 = 615397397785146428799856951317872592976325069779811900630357740743364600116099766 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 615397397785146428799856951317872592976325069779811900630357740743364600116099766 = ((75134861385319161114679106953695567577277333364346609619566247886244669224396481010703929437225754777865 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1643464247728189221623609).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 1643464247728189221623609 = 58146955411423477176677745056351683940160605230824674265581295625654125614687738 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 58146955411423477176677745056351683940160605230824674265581295625654125614687738 = ((42081577357977622002035050103974842816381499524525597922964868693950441037044553862973460117423412110823 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_22165207135937 : Nat.Prime 22165207135937 := by
  refine lucas_primality 22165207135937 (3 : ZMod 22165207135937) ?_ (fun q hq hd => ?_)
  · rw [show 22165207135937 - 1 = 22165207135936 from by norm_num]
    reduce_mod_char
  · have e : 22165207135937 - 1 = [2 ^ 6, 659 ^ 1, 1217 ^ 1, 431833 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22165207135937 - 1) / 2 = 11082603567968 from by norm_num]
      have h2 : (3 : ZMod 22165207135937) ^ 11082603567968 = ((22165207135936 : ℕ) : ZMod 22165207135937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22165207135937 - 1) / 659 = 33634608704 from by norm_num]
      have h2 : (3 : ZMod 22165207135937) ^ 33634608704 = ((2114190080833 : ℕ) : ZMod 22165207135937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22165207135937 - 1) / 1217 = 18212988608 from by norm_num]
      have h2 : (3 : ZMod 22165207135937) ^ 18212988608 = ((18628637709368 : ℕ) : ZMod 22165207135937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22165207135937 - 1) / 431833 = 51328192 from by norm_num]
      have h2 : (3 : ZMod 22165207135937) ^ 51328192 = ((1996435190482 : ℕ) : ZMod 22165207135937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_20390349929234344504446761 : Nat.Prime 20390349929234344504446761 := by
  refine lucas_primality 20390349929234344504446761 (15 : ZMod 20390349929234344504446761) ?_ (fun q hq hd => ?_)
  · rw [show 20390349929234344504446761 - 1 = 20390349929234344504446760 from by norm_num]
    reduce_mod_char
  · have e : 20390349929234344504446761 - 1 = [2 ^ 3, 5 ^ 1, 11 ^ 1, 19 ^ 1, 83 ^ 1, 1325771 ^ 1, 22165207135937 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20390349929234344504446761 - 1) / 2 = 10195174964617172252223380 from by norm_num]
      have h2 : (15 : ZMod 20390349929234344504446761) ^ 10195174964617172252223380 = ((20390349929234344504446760 : ℕ) : ZMod 20390349929234344504446761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20390349929234344504446761 - 1) / 5 = 4078069985846868900889352 from by norm_num]
      have h2 : (15 : ZMod 20390349929234344504446761) ^ 4078069985846868900889352 = ((2551796742568411525876329 : ℕ) : ZMod 20390349929234344504446761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20390349929234344504446761 - 1) / 11 = 1853668175384940409495160 from by norm_num]
      have h2 : (15 : ZMod 20390349929234344504446761) ^ 1853668175384940409495160 = ((18520607317136907937508006 : ℕ) : ZMod 20390349929234344504446761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20390349929234344504446761 - 1) / 19 = 1073176312064965500234040 from by norm_num]
      have h2 : (15 : ZMod 20390349929234344504446761) ^ 1073176312064965500234040 = ((6679348691055795369595274 : ℕ) : ZMod 20390349929234344504446761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20390349929234344504446761 - 1) / 83 = 245666866617281259089720 from by norm_num]
      have h2 : (15 : ZMod 20390349929234344504446761) ^ 245666866617281259089720 = ((8782309147795049250701249 : ℕ) : ZMod 20390349929234344504446761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20390349929234344504446761 - 1) / 1325771 = 15379993927483965560 from by norm_num]
      have h2 : (15 : ZMod 20390349929234344504446761) ^ 15379993927483965560 = ((6532293695440320723874304 : ℕ) : ZMod 20390349929234344504446761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_22165207135937).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20390349929234344504446761 - 1) / 22165207135937 = 919925981480 from by norm_num]
      have h2 : (15 : ZMod 20390349929234344504446761) ^ 919925981480 = ((7081846787961673294528998 : ℕ) : ZMod 20390349929234344504446761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3803909572078746837295094051706948091 : Nat.Prime 3803909572078746837295094051706948091 := by
  refine lucas_primality 3803909572078746837295094051706948091 (10 : ZMod 3803909572078746837295094051706948091) ?_ (fun q hq hd => ?_)
  · rw [show 3803909572078746837295094051706948091 - 1 = 3803909572078746837295094051706948090 from by norm_num]
    reduce_mod_char
  · have e : 3803909572078746837295094051706948091 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 23 ^ 1, 31 ^ 2, 353 ^ 1, 797 ^ 1, 20390349929234344504446761 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3803909572078746837295094051706948091 - 1) / 2 = 1901954786039373418647547025853474045 from by norm_num]
      have h2 : (10 : ZMod 3803909572078746837295094051706948091) ^ 1901954786039373418647547025853474045 = ((3803909572078746837295094051706948090 : ℕ) : ZMod 3803909572078746837295094051706948091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3803909572078746837295094051706948091 - 1) / 3 = 1267969857359582279098364683902316030 from by norm_num]
      have h2 : (10 : ZMod 3803909572078746837295094051706948091) ^ 1267969857359582279098364683902316030 = ((3745583752606632117355051870845043237 : ℕ) : ZMod 3803909572078746837295094051706948091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3803909572078746837295094051706948091 - 1) / 5 = 760781914415749367459018810341389618 from by norm_num]
      have h2 : (10 : ZMod 3803909572078746837295094051706948091) ^ 760781914415749367459018810341389618 = ((3653228519550324084985149043574819229 : ℕ) : ZMod 3803909572078746837295094051706948091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3803909572078746837295094051706948091 - 1) / 23 = 165387372699075949447612784856823830 from by norm_num]
      have h2 : (10 : ZMod 3803909572078746837295094051706948091) ^ 165387372699075949447612784856823830 = ((2675672524828646277826221981866427973 : ℕ) : ZMod 3803909572078746837295094051706948091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3803909572078746837295094051706948091 - 1) / 31 = 122706760389636994751454646829256390 from by norm_num]
      have h2 : (10 : ZMod 3803909572078746837295094051706948091) ^ 122706760389636994751454646829256390 = ((2035186931815633027486923752644773536 : ℕ) : ZMod 3803909572078746837295094051706948091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3803909572078746837295094051706948091 - 1) / 353 = 10775947796257073193470521392937530 from by norm_num]
      have h2 : (10 : ZMod 3803909572078746837295094051706948091) ^ 10775947796257073193470521392937530 = ((335079560218756949072620392007285377 : ℕ) : ZMod 3803909572078746837295094051706948091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3803909572078746837295094051706948091 - 1) / 797 = 4772784908505328528601121771275970 from by norm_num]
      have h2 : (10 : ZMod 3803909572078746837295094051706948091) ^ 4772784908505328528601121771275970 = ((1949079978632304296829193129571275898 : ℕ) : ZMod 3803909572078746837295094051706948091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_20390349929234344504446761).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3803909572078746837295094051706948091 - 1) / 20390349929234344504446761 = 186554403690 from by norm_num]
      have h2 : (10 : ZMod 3803909572078746837295094051706948091) ^ 186554403690 = ((2214184545814866539386645549970735903 : ℕ) : ZMod 3803909572078746837295094051706948091) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_91870409 : Nat.Prime 91870409 := by
  refine lucas_primality 91870409 (3 : ZMod 91870409) ?_ (fun q hq hd => ?_)
  · rw [show 91870409 - 1 = 91870408 from by norm_num]
    reduce_mod_char
  · have e : 91870409 - 1 = [2 ^ 3, 7 ^ 1, 37 ^ 1, 101 ^ 1, 439 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91870409 - 1) / 2 = 45935204 from by norm_num]
      have h2 : (3 : ZMod 91870409) ^ 45935204 = ((91870408 : ℕ) : ZMod 91870409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91870409 - 1) / 7 = 13124344 from by norm_num]
      have h2 : (3 : ZMod 91870409) ^ 13124344 = ((88890313 : ℕ) : ZMod 91870409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91870409 - 1) / 37 = 2482984 from by norm_num]
      have h2 : (3 : ZMod 91870409) ^ 2482984 = ((80887012 : ℕ) : ZMod 91870409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91870409 - 1) / 101 = 909608 from by norm_num]
      have h2 : (3 : ZMod 91870409) ^ 909608 = ((89823755 : ℕ) : ZMod 91870409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91870409 - 1) / 439 = 209272 from by norm_num]
      have h2 : (3 : ZMod 91870409) ^ 209272 = ((76312705 : ℕ) : ZMod 91870409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1002640523 : Nat.Prime 1002640523 := by
  refine lucas_primality 1002640523 (2 : ZMod 1002640523) ?_ (fun q hq hd => ?_)
  · rw [show 1002640523 - 1 = 1002640522 from by norm_num]
    reduce_mod_char
  · have e : 1002640523 - 1 = [2 ^ 1, 13 ^ 1, 103 ^ 1, 374399 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1002640523 - 1) / 2 = 501320261 from by norm_num]
      have h2 : (2 : ZMod 1002640523) ^ 501320261 = ((1002640522 : ℕ) : ZMod 1002640523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1002640523 - 1) / 13 = 77126194 from by norm_num]
      have h2 : (2 : ZMod 1002640523) ^ 77126194 = ((154171987 : ℕ) : ZMod 1002640523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1002640523 - 1) / 103 = 9734374 from by norm_num]
      have h2 : (2 : ZMod 1002640523) ^ 9734374 = ((426205513 : ℕ) : ZMod 1002640523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1002640523 - 1) / 374399 = 2678 from by norm_num]
      have h2 : (2 : ZMod 1002640523) ^ 2678 = ((594304286 : ℕ) : ZMod 1002640523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4195047948233 : Nat.Prime 4195047948233 := by
  refine lucas_primality 4195047948233 (3 : ZMod 4195047948233) ?_ (fun q hq hd => ?_)
  · rw [show 4195047948233 - 1 = 4195047948232 from by norm_num]
    reduce_mod_char
  · have e : 4195047948233 - 1 = [2 ^ 3, 523 ^ 1, 1002640523 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4195047948233 - 1) / 2 = 2097523974116 from by norm_num]
      have h2 : (3 : ZMod 4195047948233) ^ 2097523974116 = ((4195047948232 : ℕ) : ZMod 4195047948233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4195047948233 - 1) / 523 = 8021124184 from by norm_num]
      have h2 : (3 : ZMod 4195047948233) ^ 8021124184 = ((1114103472891 : ℕ) : ZMod 4195047948233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1002640523).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4195047948233 - 1) / 1002640523 = 4184 from by norm_num]
      have h2 : (3 : ZMod 4195047948233) ^ 4184 = ((1488871177043 : ℕ) : ZMod 4195047948233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5609122817914313723820539 : Nat.Prime 5609122817914313723820539 := by
  refine lucas_primality 5609122817914313723820539 (6 : ZMod 5609122817914313723820539) ?_ (fun q hq hd => ?_)
  · rw [show 5609122817914313723820539 - 1 = 5609122817914313723820538 from by norm_num]
    reduce_mod_char
  · have e : 5609122817914313723820539 - 1 = [2 ^ 1, 19 ^ 1, 383 ^ 1, 91870409 ^ 1, 4195047948233 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5609122817914313723820539 - 1) / 2 = 2804561408957156861910269 from by norm_num]
      have h2 : (6 : ZMod 5609122817914313723820539) ^ 2804561408957156861910269 = ((5609122817914313723820538 : ℕ) : ZMod 5609122817914313723820539) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5609122817914313723820539 - 1) / 19 = 295216990416542827569502 from by norm_num]
      have h2 : (6 : ZMod 5609122817914313723820539) ^ 295216990416542827569502 = ((5592869821890080580035658 : ℕ) : ZMod 5609122817914313723820539) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5609122817914313723820539 - 1) / 383 = 14645229289593508417286 from by norm_num]
      have h2 : (6 : ZMod 5609122817914313723820539) ^ 14645229289593508417286 = ((3845677659365211025403811 : ℕ) : ZMod 5609122817914313723820539) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_91870409).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5609122817914313723820539 - 1) / 91870409 = 61054727838583082 from by norm_num]
      have h2 : (6 : ZMod 5609122817914313723820539) ^ 61054727838583082 = ((3705136087335139166851055 : ℕ) : ZMod 5609122817914313723820539) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4195047948233).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5609122817914313723820539 - 1) / 4195047948233 = 1337081932586 from by norm_num]
      have h2 : (6 : ZMod 5609122817914313723820539) ^ 1337081932586 = ((1716320015176154010133416 : ℕ) : ZMod 5609122817914313723820539) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_168386849 : Nat.Prime 168386849 := by
  refine lucas_primality 168386849 (3 : ZMod 168386849) ?_ (fun q hq hd => ?_)
  · rw [show 168386849 - 1 = 168386848 from by norm_num]
    reduce_mod_char
  · have e : 168386849 - 1 = [2 ^ 5, 7 ^ 1, 751727 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (168386849 - 1) / 2 = 84193424 from by norm_num]
      have h2 : (3 : ZMod 168386849) ^ 84193424 = ((168386848 : ℕ) : ZMod 168386849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (168386849 - 1) / 7 = 24055264 from by norm_num]
      have h2 : (3 : ZMod 168386849) ^ 24055264 = ((101931544 : ℕ) : ZMod 168386849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (168386849 - 1) / 751727 = 224 from by norm_num]
      have h2 : (3 : ZMod 168386849) ^ 224 = ((91608833 : ℕ) : ZMod 168386849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_215530409 : Nat.Prime 215530409 := by
  refine lucas_primality 215530409 (3 : ZMod 215530409) ?_ (fun q hq hd => ?_)
  · rw [show 215530409 - 1 = 215530408 from by norm_num]
    reduce_mod_char
  · have e : 215530409 - 1 = [2 ^ 3, 461 ^ 1, 58441 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (215530409 - 1) / 2 = 107765204 from by norm_num]
      have h2 : (3 : ZMod 215530409) ^ 107765204 = ((215530408 : ℕ) : ZMod 215530409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (215530409 - 1) / 461 = 467528 from by norm_num]
      have h2 : (3 : ZMod 215530409) ^ 467528 = ((185829986 : ℕ) : ZMod 215530409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (215530409 - 1) / 58441 = 3688 from by norm_num]
      have h2 : (3 : ZMod 215530409) ^ 3688 = ((39547697 : ℕ) : ZMod 215530409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_93485380298571895397009 : Nat.Prime 93485380298571895397009 := by
  refine lucas_primality 93485380298571895397009 (3 : ZMod 93485380298571895397009) ?_ (fun q hq hd => ?_)
  · rw [show 93485380298571895397009 - 1 = 93485380298571895397008 from by norm_num]
    reduce_mod_char
  · have e : 93485380298571895397009 - 1 = [2 ^ 4, 7 ^ 1, 109 ^ 1, 211 ^ 1, 168386849 ^ 1, 215530409 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93485380298571895397009 - 1) / 2 = 46742690149285947698504 from by norm_num]
      have h2 : (3 : ZMod 93485380298571895397009) ^ 46742690149285947698504 = ((93485380298571895397008 : ℕ) : ZMod 93485380298571895397009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93485380298571895397009 - 1) / 7 = 13355054328367413628144 from by norm_num]
      have h2 : (3 : ZMod 93485380298571895397009) ^ 13355054328367413628144 = ((76953803461274649236864 : ℕ) : ZMod 93485380298571895397009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93485380298571895397009 - 1) / 109 = 857664039436439407312 from by norm_num]
      have h2 : (3 : ZMod 93485380298571895397009) ^ 857664039436439407312 = ((2217581434624029846002 : ℕ) : ZMod 93485380298571895397009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93485380298571895397009 - 1) / 211 = 443058674400814670128 from by norm_num]
      have h2 : (3 : ZMod 93485380298571895397009) ^ 443058674400814670128 = ((43384851044440988300472 : ℕ) : ZMod 93485380298571895397009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_168386849).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93485380298571895397009 - 1) / 168386849 = 555182194178192 from by norm_num]
      have h2 : (3 : ZMod 93485380298571895397009) ^ 555182194178192 = ((58097347624673154385919 : ℕ) : ZMod 93485380298571895397009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_215530409).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93485380298571895397009 - 1) / 215530409 = 433745663696912 from by norm_num]
      have h2 : (3 : ZMod 93485380298571895397009) ^ 433745663696912 = ((10613886693940522800932 : ℕ) : ZMod 93485380298571895397009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_18885983617 : Nat.Prime 18885983617 := by
  refine lucas_primality 18885983617 (15 : ZMod 18885983617) ?_ (fun q hq hd => ?_)
  · rw [show 18885983617 - 1 = 18885983616 from by norm_num]
    reduce_mod_char
  · have e : 18885983617 - 1 = [2 ^ 7, 3 ^ 2, 401 ^ 1, 40883 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18885983617 - 1) / 2 = 9442991808 from by norm_num]
      have h2 : (15 : ZMod 18885983617) ^ 9442991808 = ((18885983616 : ℕ) : ZMod 18885983617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18885983617 - 1) / 3 = 6295327872 from by norm_num]
      have h2 : (15 : ZMod 18885983617) ^ 6295327872 = ((55734618 : ℕ) : ZMod 18885983617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18885983617 - 1) / 401 = 47097216 from by norm_num]
      have h2 : (15 : ZMod 18885983617) ^ 47097216 = ((4096 : ℕ) : ZMod 18885983617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18885983617 - 1) / 40883 = 461952 from by norm_num]
      have h2 : (15 : ZMod 18885983617) ^ 461952 = ((16030710709 : ℕ) : ZMod 18885983617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1080210017 : Nat.Prime 1080210017 := by
  refine lucas_primality 1080210017 (3 : ZMod 1080210017) ?_ (fun q hq hd => ?_)
  · rw [show 1080210017 - 1 = 1080210016 from by norm_num]
    reduce_mod_char
  · have e : 1080210017 - 1 = [2 ^ 5, 33756563 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1080210017 - 1) / 2 = 540105008 from by norm_num]
      have h2 : (3 : ZMod 1080210017) ^ 540105008 = ((1080210016 : ℕ) : ZMod 1080210017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1080210017 - 1) / 33756563 = 32 from by norm_num]
      have h2 : (3 : ZMod 1080210017) ^ 32 = ((920439616 : ℕ) : ZMod 1080210017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_47529240749 : Nat.Prime 47529240749 := by
  refine lucas_primality 47529240749 (2 : ZMod 47529240749) ?_ (fun q hq hd => ?_)
  · rw [show 47529240749 - 1 = 47529240748 from by norm_num]
    reduce_mod_char
  · have e : 47529240749 - 1 = [2 ^ 2, 11 ^ 1, 1080210017 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47529240749 - 1) / 2 = 23764620374 from by norm_num]
      have h2 : (2 : ZMod 47529240749) ^ 23764620374 = ((47529240748 : ℕ) : ZMod 47529240749) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47529240749 - 1) / 11 = 4320840068 from by norm_num]
      have h2 : (2 : ZMod 47529240749) ^ 4320840068 = ((19731128624 : ℕ) : ZMod 47529240749) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1080210017).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47529240749 - 1) / 1080210017 = 44 from by norm_num]
      have h2 : (2 : ZMod 47529240749) ^ 44 = ((6366967286 : ℕ) : ZMod 47529240749) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3178641606717935496778334833 : Nat.Prime 3178641606717935496778334833 := by
  refine lucas_primality 3178641606717935496778334833 (11 : ZMod 3178641606717935496778334833) ?_ (fun q hq hd => ?_)
  · rw [show 3178641606717935496778334833 - 1 = 3178641606717935496778334832 from by norm_num]
    reduce_mod_char
  · have e : 3178641606717935496778334833 - 1 = [2 ^ 4, 3 ^ 1, 31 ^ 1, 59 ^ 1, 401 ^ 1, 6451 ^ 1, 294479 ^ 1, 47529240749 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3178641606717935496778334833 - 1) / 2 = 1589320803358967748389167416 from by norm_num]
      have h2 : (11 : ZMod 3178641606717935496778334833) ^ 1589320803358967748389167416 = ((3178641606717935496778334832 : ℕ) : ZMod 3178641606717935496778334833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3178641606717935496778334833 - 1) / 3 = 1059547202239311832259444944 from by norm_num]
      have h2 : (11 : ZMod 3178641606717935496778334833) ^ 1059547202239311832259444944 = ((445834767858520306382091050 : ℕ) : ZMod 3178641606717935496778334833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3178641606717935496778334833 - 1) / 31 = 102536826023159209573494672 from by norm_num]
      have h2 : (11 : ZMod 3178641606717935496778334833) ^ 102536826023159209573494672 = ((2899858951295049085246872639 : ℕ) : ZMod 3178641606717935496778334833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3178641606717935496778334833 - 1) / 59 = 53875281469795516894548048 from by norm_num]
      have h2 : (11 : ZMod 3178641606717935496778334833) ^ 53875281469795516894548048 = ((1897132815950272178901864327 : ℕ) : ZMod 3178641606717935496778334833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3178641606717935496778334833 - 1) / 401 = 7926787049171908969522032 from by norm_num]
      have h2 : (11 : ZMod 3178641606717935496778334833) ^ 7926787049171908969522032 = ((1528015296321092750445163695 : ℕ) : ZMod 3178641606717935496778334833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3178641606717935496778334833 - 1) / 6451 = 492736258985883660948432 from by norm_num]
      have h2 : (11 : ZMod 3178641606717935496778334833) ^ 492736258985883660948432 = ((134078135556626356539964649 : ℕ) : ZMod 3178641606717935496778334833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3178641606717935496778334833 - 1) / 294479 = 10794119807245798501008 from by norm_num]
      have h2 : (11 : ZMod 3178641606717935496778334833) ^ 10794119807245798501008 = ((2283957718093700498191297632 : ℕ) : ZMod 3178641606717935496778334833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_47529240749).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3178641606717935496778334833 - 1) / 47529240749 = 66877601169861168 from by norm_num]
      have h2 : (11 : ZMod 3178641606717935496778334833) ^ 66877601169861168 = ((269729190764052759165585471 : ℕ) : ZMod 3178641606717935496778334833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_37452571239931 : Nat.Prime 37452571239931 := by
  refine lucas_primality 37452571239931 (3 : ZMod 37452571239931) ?_ (fun q hq hd => ?_)
  · rw [show 37452571239931 - 1 = 37452571239930 from by norm_num]
    reduce_mod_char
  · have e : 37452571239931 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 7 ^ 2, 11 ^ 1, 211 ^ 1, 431 ^ 1, 25469 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37452571239931 - 1) / 2 = 18726285619965 from by norm_num]
      have h2 : (3 : ZMod 37452571239931) ^ 18726285619965 = ((37452571239930 : ℕ) : ZMod 37452571239931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37452571239931 - 1) / 3 = 12484190413310 from by norm_num]
      have h2 : (3 : ZMod 37452571239931) ^ 12484190413310 = ((22162211610019 : ℕ) : ZMod 37452571239931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37452571239931 - 1) / 5 = 7490514247986 from by norm_num]
      have h2 : (3 : ZMod 37452571239931) ^ 7490514247986 = ((21575324213146 : ℕ) : ZMod 37452571239931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37452571239931 - 1) / 7 = 5350367319990 from by norm_num]
      have h2 : (3 : ZMod 37452571239931) ^ 5350367319990 = ((15185452871492 : ℕ) : ZMod 37452571239931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37452571239931 - 1) / 11 = 3404779203630 from by norm_num]
      have h2 : (3 : ZMod 37452571239931) ^ 3404779203630 = ((20691070315855 : ℕ) : ZMod 37452571239931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37452571239931 - 1) / 211 = 177500337630 from by norm_num]
      have h2 : (3 : ZMod 37452571239931) ^ 177500337630 = ((18039431208837 : ℕ) : ZMod 37452571239931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37452571239931 - 1) / 431 = 86896917030 from by norm_num]
      have h2 : (3 : ZMod 37452571239931) ^ 86896917030 = ((27959237888340 : ℕ) : ZMod 37452571239931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37452571239931 - 1) / 25469 = 1470515970 from by norm_num]
      have h2 : (3 : ZMod 37452571239931) ^ 1470515970 = ((4416996620142 : ℕ) : ZMod 37452571239931) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_489333371 : Nat.Prime 489333371 := by
  refine lucas_primality 489333371 (6 : ZMod 489333371) ?_ (fun q hq hd => ?_)
  · rw [show 489333371 - 1 = 489333370 from by norm_num]
    reduce_mod_char
  · have e : 489333371 - 1 = [2 ^ 1, 5 ^ 1, 443 ^ 1, 110459 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (489333371 - 1) / 2 = 244666685 from by norm_num]
      have h2 : (6 : ZMod 489333371) ^ 244666685 = ((489333370 : ℕ) : ZMod 489333371) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (489333371 - 1) / 5 = 97866674 from by norm_num]
      have h2 : (6 : ZMod 489333371) ^ 97866674 = ((470263448 : ℕ) : ZMod 489333371) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (489333371 - 1) / 443 = 1104590 from by norm_num]
      have h2 : (6 : ZMod 489333371) ^ 1104590 = ((90454410 : ℕ) : ZMod 489333371) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (489333371 - 1) / 110459 = 4430 from by norm_num]
      have h2 : (6 : ZMod 489333371) ^ 4430 = ((177951636 : ℕ) : ZMod 489333371) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_45957593887 : Nat.Prime 45957593887 := by
  refine lucas_primality 45957593887 (3 : ZMod 45957593887) ?_ (fun q hq hd => ?_)
  · rw [show 45957593887 - 1 = 45957593886 from by norm_num]
    reduce_mod_char
  · have e : 45957593887 - 1 = [2 ^ 1, 3 ^ 1, 127 ^ 1, 4903 ^ 1, 12301 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45957593887 - 1) / 2 = 22978796943 from by norm_num]
      have h2 : (3 : ZMod 45957593887) ^ 22978796943 = ((45957593886 : ℕ) : ZMod 45957593887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45957593887 - 1) / 3 = 15319197962 from by norm_num]
      have h2 : (3 : ZMod 45957593887) ^ 15319197962 = ((28708269382 : ℕ) : ZMod 45957593887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45957593887 - 1) / 127 = 361870818 from by norm_num]
      have h2 : (3 : ZMod 45957593887) ^ 361870818 = ((35806420901 : ℕ) : ZMod 45957593887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45957593887 - 1) / 4903 = 9373362 from by norm_num]
      have h2 : (3 : ZMod 45957593887) ^ 9373362 = ((45682990762 : ℕ) : ZMod 45957593887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45957593887 - 1) / 12301 = 3736086 from by norm_num]
      have h2 : (3 : ZMod 45957593887) ^ 3736086 = ((9584936920 : ℕ) : ZMod 45957593887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_25644337388947 : Nat.Prime 25644337388947 := by
  refine lucas_primality 25644337388947 (2 : ZMod 25644337388947) ?_ (fun q hq hd => ?_)
  · rw [show 25644337388947 - 1 = 25644337388946 from by norm_num]
    reduce_mod_char
  · have e : 25644337388947 - 1 = [2 ^ 1, 3 ^ 2, 31 ^ 1, 45957593887 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25644337388947 - 1) / 2 = 12822168694473 from by norm_num]
      have h2 : (2 : ZMod 25644337388947) ^ 12822168694473 = ((25644337388946 : ℕ) : ZMod 25644337388947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25644337388947 - 1) / 3 = 8548112462982 from by norm_num]
      have h2 : (2 : ZMod 25644337388947) ^ 8548112462982 = ((25339664607083 : ℕ) : ZMod 25644337388947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25644337388947 - 1) / 31 = 827236689966 from by norm_num]
      have h2 : (2 : ZMod 25644337388947) ^ 827236689966 = ((17878850421492 : ℕ) : ZMod 25644337388947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_45957593887).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25644337388947 - 1) / 45957593887 = 558 from by norm_num]
      have h2 : (2 : ZMod 25644337388947) ^ 558 = ((7870999102743 : ℕ) : ZMod 25644337388947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_99759313 : Nat.Prime 99759313 := by
  refine lucas_primality 99759313 (7 : ZMod 99759313) ?_ (fun q hq hd => ?_)
  · rw [show 99759313 - 1 = 99759312 from by norm_num]
    reduce_mod_char
  · have e : 99759313 - 1 = [2 ^ 4, 3 ^ 2, 43 ^ 1, 16111 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99759313 - 1) / 2 = 49879656 from by norm_num]
      have h2 : (7 : ZMod 99759313) ^ 49879656 = ((99759312 : ℕ) : ZMod 99759313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99759313 - 1) / 3 = 33253104 from by norm_num]
      have h2 : (7 : ZMod 99759313) ^ 33253104 = ((93399006 : ℕ) : ZMod 99759313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99759313 - 1) / 43 = 2319984 from by norm_num]
      have h2 : (7 : ZMod 99759313) ^ 2319984 = ((53053794 : ℕ) : ZMod 99759313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (99759313 - 1) / 16111 = 6192 from by norm_num]
      have h2 : (7 : ZMod 99759313) ^ 6192 = ((96692162 : ℕ) : ZMod 99759313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_53870029021 : Nat.Prime 53870029021 := by
  refine lucas_primality 53870029021 (10 : ZMod 53870029021) ?_ (fun q hq hd => ?_)
  · rw [show 53870029021 - 1 = 53870029020 from by norm_num]
    reduce_mod_char
  · have e : 53870029021 - 1 = [2 ^ 2, 3 ^ 3, 5 ^ 1, 99759313 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53870029021 - 1) / 2 = 26935014510 from by norm_num]
      have h2 : (10 : ZMod 53870029021) ^ 26935014510 = ((53870029020 : ℕ) : ZMod 53870029021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53870029021 - 1) / 3 = 17956676340 from by norm_num]
      have h2 : (10 : ZMod 53870029021) ^ 17956676340 = ((13019395619 : ℕ) : ZMod 53870029021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53870029021 - 1) / 5 = 10774005804 from by norm_num]
      have h2 : (10 : ZMod 53870029021) ^ 10774005804 = ((17731960944 : ℕ) : ZMod 53870029021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_99759313).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (53870029021 - 1) / 99759313 = 540 from by norm_num]
      have h2 : (10 : ZMod 53870029021) ^ 540 = ((31533719693 : ℕ) : ZMod 53870029021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6224050496636423881 : Nat.Prime 6224050496636423881 := by
  refine lucas_primality 6224050496636423881 (19 : ZMod 6224050496636423881) ?_ (fun q hq hd => ?_)
  · rw [show 6224050496636423881 - 1 = 6224050496636423880 from by norm_num]
    reduce_mod_char
  · have e : 6224050496636423881 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 11 ^ 1, 13 ^ 1, 6733 ^ 1, 53870029021 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6224050496636423881 - 1) / 2 = 3112025248318211940 from by norm_num]
      have h2 : (19 : ZMod 6224050496636423881) ^ 3112025248318211940 = ((6224050496636423880 : ℕ) : ZMod 6224050496636423881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6224050496636423881 - 1) / 3 = 2074683498878807960 from by norm_num]
      have h2 : (19 : ZMod 6224050496636423881) ^ 2074683498878807960 = ((3321705053511573237 : ℕ) : ZMod 6224050496636423881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6224050496636423881 - 1) / 5 = 1244810099327284776 from by norm_num]
      have h2 : (19 : ZMod 6224050496636423881) ^ 1244810099327284776 = ((3582222004901432003 : ℕ) : ZMod 6224050496636423881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6224050496636423881 - 1) / 11 = 565822772421493080 from by norm_num]
      have h2 : (19 : ZMod 6224050496636423881) ^ 565822772421493080 = ((2437466837485539852 : ℕ) : ZMod 6224050496636423881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6224050496636423881 - 1) / 13 = 478773115125878760 from by norm_num]
      have h2 : (19 : ZMod 6224050496636423881) ^ 478773115125878760 = ((5897636926162278071 : ℕ) : ZMod 6224050496636423881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6224050496636423881 - 1) / 6733 = 924409698000360 from by norm_num]
      have h2 : (19 : ZMod 6224050496636423881) ^ 924409698000360 = ((4538412261093804455 : ℕ) : ZMod 6224050496636423881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_53870029021).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6224050496636423881 - 1) / 53870029021 = 115538280 from by norm_num]
      have h2 : (19 : ZMod 6224050496636423881) ^ 115538280 = ((5289059547790477948 : ℕ) : ZMod 6224050496636423881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_86937537337017568769809 : Nat.Prime 86937537337017568769809 := by
  refine lucas_primality 86937537337017568769809 (7 : ZMod 86937537337017568769809) ?_ (fun q hq hd => ?_)
  · rw [show 86937537337017568769809 - 1 = 86937537337017568769808 from by norm_num]
    reduce_mod_char
  · have e : 86937537337017568769809 - 1 = [2 ^ 4, 3 ^ 2, 97 ^ 1, 6224050496636423881 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86937537337017568769809 - 1) / 2 = 43468768668508784384904 from by norm_num]
      have h2 : (7 : ZMod 86937537337017568769809) ^ 43468768668508784384904 = ((86937537337017568769808 : ℕ) : ZMod 86937537337017568769809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86937537337017568769809 - 1) / 3 = 28979179112339189589936 from by norm_num]
      have h2 : (7 : ZMod 86937537337017568769809) ^ 28979179112339189589936 = ((66840075858722348126077 : ℕ) : ZMod 86937537337017568769809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86937537337017568769809 - 1) / 97 = 896263271515645038864 from by norm_num]
      have h2 : (7 : ZMod 86937537337017568769809) ^ 896263271515645038864 = ((62562899236947345964484 : ℕ) : ZMod 86937537337017568769809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6224050496636423881).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86937537337017568769809 - 1) / 6224050496636423881 = 13968 from by norm_num]
      have h2 : (7 : ZMod 86937537337017568769809) ^ 13968 = ((65731505469662324555251 : ℕ) : ZMod 86937537337017568769809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8159927869564849092796028544559 : Nat.Prime 8159927869564849092796028544559 := by
  refine lucas_primality 8159927869564849092796028544559 (3 : ZMod 8159927869564849092796028544559) ?_ (fun q hq hd => ?_)
  · rw [show 8159927869564849092796028544559 - 1 = 8159927869564849092796028544558 from by norm_num]
    reduce_mod_char
  · have e : 8159927869564849092796028544559 - 1 = [2 ^ 1, 3 ^ 1, 13 ^ 1, 1203329 ^ 1, 86937537337017568769809 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8159927869564849092796028544559 - 1) / 2 = 4079963934782424546398014272279 from by norm_num]
      have h2 : (3 : ZMod 8159927869564849092796028544559) ^ 4079963934782424546398014272279 = ((8159927869564849092796028544558 : ℕ) : ZMod 8159927869564849092796028544559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8159927869564849092796028544559 - 1) / 3 = 2719975956521616364265342848186 from by norm_num]
      have h2 : (3 : ZMod 8159927869564849092796028544559) ^ 2719975956521616364265342848186 = ((8059014972772466934863899279737 : ℕ) : ZMod 8159927869564849092796028544559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8159927869564849092796028544559 - 1) / 13 = 627686759197296084061232964966 from by norm_num]
      have h2 : (3 : ZMod 8159927869564849092796028544559) ^ 627686759197296084061232964966 = ((1458518860554313306493856694609 : ℕ) : ZMod 8159927869564849092796028544559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8159927869564849092796028544559 - 1) / 1203329 = 6781127912287370364045102 from by norm_num]
      have h2 : (3 : ZMod 8159927869564849092796028544559) ^ 6781127912287370364045102 = ((7343770185107612270486987399402 : ℕ) : ZMod 8159927869564849092796028544559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_86937537337017568769809).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8159927869564849092796028544559 - 1) / 86937537337017568769809 = 93859662 from by norm_num]
      have h2 : (3 : ZMod 8159927869564849092796028544559) ^ 93859662 = ((2485505918906238709834511387925 : ℕ) : ZMod 8159927869564849092796028544559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6885357560205319573060633896800918448254904729193 : Nat.Prime 6885357560205319573060633896800918448254904729193 := by
  refine lucas_primality 6885357560205319573060633896800918448254904729193 (5 : ZMod 6885357560205319573060633896800918448254904729193) ?_ (fun q hq hd => ?_)
  · rw [show 6885357560205319573060633896800918448254904729193 - 1 = 6885357560205319573060633896800918448254904729192 from by norm_num]
    reduce_mod_char
  · have e : 6885357560205319573060633896800918448254904729193 - 1 = [2 ^ 3, 3 ^ 2, 457 ^ 1, 25644337388947 ^ 1, 8159927869564849092796028544559 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6885357560205319573060633896800918448254904729193 - 1) / 2 = 3442678780102659786530316948400459224127452364596 from by norm_num]
      have h2 : (5 : ZMod 6885357560205319573060633896800918448254904729193) ^ 3442678780102659786530316948400459224127452364596 = ((6885357560205319573060633896800918448254904729192 : ℕ) : ZMod 6885357560205319573060633896800918448254904729193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6885357560205319573060633896800918448254904729193 - 1) / 3 = 2295119186735106524353544632266972816084968243064 from by norm_num]
      have h2 : (5 : ZMod 6885357560205319573060633896800918448254904729193) ^ 2295119186735106524353544632266972816084968243064 = ((6085191249325610246747244076296924220523512299807 : ℕ) : ZMod 6885357560205319573060633896800918448254904729193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6885357560205319573060633896800918448254904729193 - 1) / 457 = 15066427921674659897288039161489974722658434856 from by norm_num]
      have h2 : (5 : ZMod 6885357560205319573060633896800918448254904729193) ^ 15066427921674659897288039161489974722658434856 = ((6885357560205319573060633896764024960107485625961 : ℕ) : ZMod 6885357560205319573060633896800918448254904729193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_25644337388947).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6885357560205319573060633896800918448254904729193 - 1) / 25644337388947 = 268494266620161794549360523230169336 from by norm_num]
      have h2 : (5 : ZMod 6885357560205319573060633896800918448254904729193) ^ 268494266620161794549360523230169336 = ((168467469555089816165691774997874145040543651812 : ℕ) : ZMod 6885357560205319573060633896800918448254904729193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_8159927869564849092796028544559).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6885357560205319573060633896800918448254904729193 - 1) / 8159927869564849092796028544559 = 843801277445912088 from by norm_num]
      have h2 : (5 : ZMod 6885357560205319573060633896800918448254904729193) ^ 843801277445912088 = ((1493017507530580566076876060163012971536522097951 : ℕ) : ZMod 6885357560205319573060633896800918448254904729193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_989482187915659 : Nat.Prime 989482187915659 := by
  refine lucas_primality 989482187915659 (2 : ZMod 989482187915659) ?_ (fun q hq hd => ?_)
  · rw [show 989482187915659 - 1 = 989482187915658 from by norm_num]
    reduce_mod_char
  · have e : 989482187915659 - 1 = [2 ^ 1, 3 ^ 2, 17 ^ 1, 1951 ^ 1, 15271 ^ 1, 108533 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (989482187915659 - 1) / 2 = 494741093957829 from by norm_num]
      have h2 : (2 : ZMod 989482187915659) ^ 494741093957829 = ((989482187915658 : ℕ) : ZMod 989482187915659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (989482187915659 - 1) / 3 = 329827395971886 from by norm_num]
      have h2 : (2 : ZMod 989482187915659) ^ 329827395971886 = ((699661677927287 : ℕ) : ZMod 989482187915659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (989482187915659 - 1) / 17 = 58204834583274 from by norm_num]
      have h2 : (2 : ZMod 989482187915659) ^ 58204834583274 = ((759908415556546 : ℕ) : ZMod 989482187915659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (989482187915659 - 1) / 1951 = 507166677558 from by norm_num]
      have h2 : (2 : ZMod 989482187915659) ^ 507166677558 = ((437305369660264 : ℕ) : ZMod 989482187915659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (989482187915659 - 1) / 15271 = 64794852198 from by norm_num]
      have h2 : (2 : ZMod 989482187915659) ^ 64794852198 = ((357119134339490 : ℕ) : ZMod 989482187915659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (989482187915659 - 1) / 108533 = 9116878626 from by norm_num]
      have h2 : (2 : ZMod 989482187915659) ^ 9116878626 = ((697060624079736 : ℕ) : ZMod 989482187915659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_23747572509975817 : Nat.Prime 23747572509975817 := by
  refine lucas_primality 23747572509975817 (5 : ZMod 23747572509975817) ?_ (fun q hq hd => ?_)
  · rw [show 23747572509975817 - 1 = 23747572509975816 from by norm_num]
    reduce_mod_char
  · have e : 23747572509975817 - 1 = [2 ^ 3, 3 ^ 1, 989482187915659 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23747572509975817 - 1) / 2 = 11873786254987908 from by norm_num]
      have h2 : (5 : ZMod 23747572509975817) ^ 11873786254987908 = ((23747572509975816 : ℕ) : ZMod 23747572509975817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23747572509975817 - 1) / 3 = 7915857503325272 from by norm_num]
      have h2 : (5 : ZMod 23747572509975817) ^ 7915857503325272 = ((23720808522914544 : ℕ) : ZMod 23747572509975817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_989482187915659).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23747572509975817 - 1) / 989482187915659 = 24 from by norm_num]
      have h2 : (5 : ZMod 23747572509975817) ^ 24 = ((12109499755438991 : ℕ) : ZMod 23747572509975817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11310921291356461685467 : Nat.Prime 11310921291356461685467 := by
  refine lucas_primality 11310921291356461685467 (2 : ZMod 11310921291356461685467) ?_ (fun q hq hd => ?_)
  · rw [show 11310921291356461685467 - 1 = 11310921291356461685466 from by norm_num]
    reduce_mod_char
  · have e : 11310921291356461685467 - 1 = [2 ^ 1, 3 ^ 2, 47 ^ 1, 563 ^ 1, 23747572509975817 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11310921291356461685467 - 1) / 2 = 5655460645678230842733 from by norm_num]
      have h2 : (2 : ZMod 11310921291356461685467) ^ 5655460645678230842733 = ((11310921291356461685466 : ℕ) : ZMod 11310921291356461685467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11310921291356461685467 - 1) / 3 = 3770307097118820561822 from by norm_num]
      have h2 : (2 : ZMod 11310921291356461685467) ^ 3770307097118820561822 = ((10590018408084229803579 : ℕ) : ZMod 11310921291356461685467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11310921291356461685467 - 1) / 47 = 240657899816094929478 from by norm_num]
      have h2 : (2 : ZMod 11310921291356461685467) ^ 240657899816094929478 = ((1621700033093612202413 : ℕ) : ZMod 11310921291356461685467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11310921291356461685467 - 1) / 563 = 20090446343439541182 from by norm_num]
      have h2 : (2 : ZMod 11310921291356461685467) ^ 20090446343439541182 = ((3458785179214154176627 : ℕ) : ZMod 11310921291356461685467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_23747572509975817).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11310921291356461685467 - 1) / 23747572509975817 = 476298 from by norm_num]
      have h2 : (2 : ZMod 11310921291356461685467) ^ 476298 = ((1463405084698702346016 : ℕ) : ZMod 11310921291356461685467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_514805271654797997152345039 : Nat.Prime 514805271654797997152345039 := by
  refine lucas_primality 514805271654797997152345039 (21 : ZMod 514805271654797997152345039) ?_ (fun q hq hd => ?_)
  · rw [show 514805271654797997152345039 - 1 = 514805271654797997152345038 from by norm_num]
    reduce_mod_char
  · have e : 514805271654797997152345039 - 1 = [2 ^ 1, 7 ^ 1, 3251 ^ 1, 11310921291356461685467 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (514805271654797997152345039 - 1) / 2 = 257402635827398998576172519 from by norm_num]
      have h2 : (21 : ZMod 514805271654797997152345039) ^ 257402635827398998576172519 = ((514805271654797997152345038 : ℕ) : ZMod 514805271654797997152345039) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (514805271654797997152345039 - 1) / 7 = 73543610236399713878906434 from by norm_num]
      have h2 : (21 : ZMod 514805271654797997152345039) ^ 73543610236399713878906434 = ((124026913649984238263279233 : ℕ) : ZMod 514805271654797997152345039) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (514805271654797997152345039 - 1) / 3251 = 158352898078990463596538 from by norm_num]
      have h2 : (21 : ZMod 514805271654797997152345039) ^ 158352898078990463596538 = ((180851378688345601201912848 : ℕ) : ZMod 514805271654797997152345039) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_11310921291356461685467).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (514805271654797997152345039 - 1) / 11310921291356461685467 = 45514 from by norm_num]
      have h2 : (21 : ZMod 514805271654797997152345039) ^ 45514 = ((101777047966460128700770681 : ℕ) : ZMod 514805271654797997152345039) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_88119307925269041107418404833666787 : Nat.Prime 88119307925269041107418404833666787 := by
  refine lucas_primality 88119307925269041107418404833666787 (5 : ZMod 88119307925269041107418404833666787) ?_ (fun q hq hd => ?_)
  · rw [show 88119307925269041107418404833666787 - 1 = 88119307925269041107418404833666786 from by norm_num]
    reduce_mod_char
  · have e : 88119307925269041107418404833666787 - 1 = [2 ^ 1, 7 ^ 1, 463 ^ 1, 26407 ^ 1, 514805271654797997152345039 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88119307925269041107418404833666787 - 1) / 2 = 44059653962634520553709202416833393 from by norm_num]
      have h2 : (5 : ZMod 88119307925269041107418404833666787) ^ 44059653962634520553709202416833393 = ((88119307925269041107418404833666786 : ℕ) : ZMod 88119307925269041107418404833666787) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88119307925269041107418404833666787 - 1) / 7 = 12588472560752720158202629261952398 from by norm_num]
      have h2 : (5 : ZMod 88119307925269041107418404833666787) ^ 12588472560752720158202629261952398 = ((2553284067472293253712456370548407 : ℕ) : ZMod 88119307925269041107418404833666787) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88119307925269041107418404833666787 - 1) / 463 = 190322479320235509951227656228222 from by norm_num]
      have h2 : (5 : ZMod 88119307925269041107418404833666787) ^ 190322479320235509951227656228222 = ((62366048793361377230835610431437099 : ℕ) : ZMod 88119307925269041107418404833666787) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88119307925269041107418404833666787 - 1) / 26407 = 3336967770866400617541500542798 from by norm_num]
      have h2 : (5 : ZMod 88119307925269041107418404833666787) ^ 3336967770866400617541500542798 = ((41702599376404021344437593149282323 : ℕ) : ZMod 88119307925269041107418404833666787) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_514805271654797997152345039).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88119307925269041107418404833666787 - 1) / 514805271654797997152345039 = 171170174 from by norm_num]
      have h2 : (5 : ZMod 88119307925269041107418404833666787) ^ 171170174 = ((71768804005475758420273974891399664 : ℕ) : ZMod 88119307925269041107418404833666787) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_48919673417 : Nat.Prime 48919673417 := by
  refine lucas_primality 48919673417 (3 : ZMod 48919673417) ?_ (fun q hq hd => ?_)
  · rw [show 48919673417 - 1 = 48919673416 from by norm_num]
    reduce_mod_char
  · have e : 48919673417 - 1 = [2 ^ 3, 17 ^ 1, 349 ^ 1, 467 ^ 1, 2207 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48919673417 - 1) / 2 = 24459836708 from by norm_num]
      have h2 : (3 : ZMod 48919673417) ^ 24459836708 = ((48919673416 : ℕ) : ZMod 48919673417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48919673417 - 1) / 17 = 2877627848 from by norm_num]
      have h2 : (3 : ZMod 48919673417) ^ 2877627848 = ((2889449763 : ℕ) : ZMod 48919673417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48919673417 - 1) / 349 = 140170984 from by norm_num]
      have h2 : (3 : ZMod 48919673417) ^ 140170984 = ((33105389079 : ℕ) : ZMod 48919673417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48919673417 - 1) / 467 = 104753048 from by norm_num]
      have h2 : (3 : ZMod 48919673417) ^ 104753048 = ((27519556733 : ℕ) : ZMod 48919673417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48919673417 - 1) / 2207 = 22165688 from by norm_num]
      have h2 : (3 : ZMod 48919673417) ^ 22165688 = ((48313028113 : ℕ) : ZMod 48919673417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_104626809569 : Nat.Prime 104626809569 := by
  refine lucas_primality 104626809569 (3 : ZMod 104626809569) ?_ (fun q hq hd => ?_)
  · rw [show 104626809569 - 1 = 104626809568 from by norm_num]
    reduce_mod_char
  · have e : 104626809569 - 1 = [2 ^ 5, 1621 ^ 1, 2017019 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104626809569 - 1) / 2 = 52313404784 from by norm_num]
      have h2 : (3 : ZMod 104626809569) ^ 52313404784 = ((104626809568 : ℕ) : ZMod 104626809569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104626809569 - 1) / 1621 = 64544608 from by norm_num]
      have h2 : (3 : ZMod 104626809569) ^ 64544608 = ((55919846961 : ℕ) : ZMod 104626809569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104626809569 - 1) / 2017019 = 51872 from by norm_num]
      have h2 : (3 : ZMod 104626809569) ^ 51872 = ((63848625887 : ℕ) : ZMod 104626809569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3094617845789 : Nat.Prime 3094617845789 := by
  refine lucas_primality 3094617845789 (2 : ZMod 3094617845789) ?_ (fun q hq hd => ?_)
  · rw [show 3094617845789 - 1 = 3094617845788 from by norm_num]
    reduce_mod_char
  · have e : 3094617845789 - 1 = [2 ^ 2, 7 ^ 1, 40693 ^ 1, 2715997 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3094617845789 - 1) / 2 = 1547308922894 from by norm_num]
      have h2 : (2 : ZMod 3094617845789) ^ 1547308922894 = ((3094617845788 : ℕ) : ZMod 3094617845789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3094617845789 - 1) / 7 = 442088263684 from by norm_num]
      have h2 : (2 : ZMod 3094617845789) ^ 442088263684 = ((156449476756 : ℕ) : ZMod 3094617845789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3094617845789 - 1) / 40693 = 76047916 from by norm_num]
      have h2 : (2 : ZMod 3094617845789) ^ 76047916 = ((1676138751398 : ℕ) : ZMod 3094617845789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3094617845789 - 1) / 2715997 = 1139404 from by norm_num]
      have h2 : (2 : ZMod 3094617845789) ^ 1139404 = ((2687257597913 : ℕ) : ZMod 3094617845789) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1942679952241168269329647 : Nat.Prime 1942679952241168269329647 := by
  refine lucas_primality 1942679952241168269329647 (3 : ZMod 1942679952241168269329647) ?_ (fun q hq hd => ?_)
  · rw [show 1942679952241168269329647 - 1 = 1942679952241168269329646 from by norm_num]
    reduce_mod_char
  · have e : 1942679952241168269329647 - 1 = [2 ^ 1, 3 ^ 1, 104626809569 ^ 1, 3094617845789 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1942679952241168269329647 - 1) / 2 = 971339976120584134664823 from by norm_num]
      have h2 : (3 : ZMod 1942679952241168269329647) ^ 971339976120584134664823 = ((1942679952241168269329646 : ℕ) : ZMod 1942679952241168269329647) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1942679952241168269329647 - 1) / 3 = 647559984080389423109882 from by norm_num]
      have h2 : (3 : ZMod 1942679952241168269329647) ^ 647559984080389423109882 = ((1396013766995975583686350 : ℕ) : ZMod 1942679952241168269329647) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_104626809569).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1942679952241168269329647 - 1) / 104626809569 = 18567707074734 from by norm_num]
      have h2 : (3 : ZMod 1942679952241168269329647) ^ 18567707074734 = ((517187493542518532891657 : ℕ) : ZMod 1942679952241168269329647) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3094617845789).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1942679952241168269329647 - 1) / 3094617845789 = 627760857414 from by norm_num]
      have h2 : (3 : ZMod 1942679952241168269329647) ^ 627760857414 = ((43916085503920369696180 : ℕ) : ZMod 1942679952241168269329647) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_54657255048286677488033160851148008819 : Nat.Prime 54657255048286677488033160851148008819 := by
  refine lucas_primality 54657255048286677488033160851148008819 (6 : ZMod 54657255048286677488033160851148008819) ?_ (fun q hq hd => ?_)
  · rw [show 54657255048286677488033160851148008819 - 1 = 54657255048286677488033160851148008818 from by norm_num]
    reduce_mod_char
  · have e : 54657255048286677488033160851148008819 - 1 = [2 ^ 1, 13 ^ 1, 479 ^ 1, 719 ^ 1, 3142019 ^ 1, 1942679952241168269329647 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54657255048286677488033160851148008819 - 1) / 2 = 27328627524143338744016580425574004409 from by norm_num]
      have h2 : (6 : ZMod 54657255048286677488033160851148008819) ^ 27328627524143338744016580425574004409 = ((54657255048286677488033160851148008818 : ℕ) : ZMod 54657255048286677488033160851148008819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54657255048286677488033160851148008819 - 1) / 13 = 4204404234483590576002550834703692986 from by norm_num]
      have h2 : (6 : ZMod 54657255048286677488033160851148008819) ^ 4204404234483590576002550834703692986 = ((17076798185516881619211580714210682746 : ℕ) : ZMod 54657255048286677488033160851148008819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54657255048286677488033160851148008819 - 1) / 479 = 114107004276172604359150648958555342 from by norm_num]
      have h2 : (6 : ZMod 54657255048286677488033160851148008819) ^ 114107004276172604359150648958555342 = ((42908133199899392803255685891501036155 : ℕ) : ZMod 54657255048286677488033160851148008819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54657255048286677488033160851148008819 - 1) / 719 = 76018435394000942264302031781847022 from by norm_num]
      have h2 : (6 : ZMod 54657255048286677488033160851148008819) ^ 76018435394000942264302031781847022 = ((23672122982487934848082534412306559728 : ℕ) : ZMod 54657255048286677488033160851148008819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54657255048286677488033160851148008819 - 1) / 3142019 = 17395583874027075421260393667622 from by norm_num]
      have h2 : (6 : ZMod 54657255048286677488033160851148008819) ^ 17395583874027075421260393667622 = ((29195484581624814317445190280961324552 : ℕ) : ZMod 54657255048286677488033160851148008819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1942679952241168269329647).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54657255048286677488033160851148008819 - 1) / 1942679952241168269329647 = 28134976626094 from by norm_num]
      have h2 : (6 : ZMod 54657255048286677488033160851148008819) ^ 28134976626094 = ((26014596980834109287986881275270280492 : ℕ) : ZMod 54657255048286677488033160851148008819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1311493493 : Nat.Prime 1311493493 := by
  refine lucas_primality 1311493493 (2 : ZMod 1311493493) ?_ (fun q hq hd => ?_)
  · rw [show 1311493493 - 1 = 1311493492 from by norm_num]
    reduce_mod_char
  · have e : 1311493493 - 1 = [2 ^ 2, 17 ^ 1, 19286669 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1311493493 - 1) / 2 = 655746746 from by norm_num]
      have h2 : (2 : ZMod 1311493493) ^ 655746746 = ((1311493492 : ℕ) : ZMod 1311493493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1311493493 - 1) / 17 = 77146676 from by norm_num]
      have h2 : (2 : ZMod 1311493493) ^ 77146676 = ((925634612 : ℕ) : ZMod 1311493493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1311493493 - 1) / 19286669 = 68 from by norm_num]
      have h2 : (2 : ZMod 1311493493) ^ 68 = ((1285805941 : ℕ) : ZMod 1311493493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2622986987 : Nat.Prime 2622986987 := by
  refine lucas_primality 2622986987 (2 : ZMod 2622986987) ?_ (fun q hq hd => ?_)
  · rw [show 2622986987 - 1 = 2622986986 from by norm_num]
    reduce_mod_char
  · have e : 2622986987 - 1 = [2 ^ 1, 1311493493 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2622986987 - 1) / 2 = 1311493493 from by norm_num]
      have h2 : (2 : ZMod 2622986987) ^ 1311493493 = ((2622986986 : ℕ) : ZMod 2622986987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1311493493).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2622986987 - 1) / 1311493493 = 2 from by norm_num]
      have h2 : (2 : ZMod 2622986987) ^ 2 = ((4 : ℕ) : ZMod 2622986987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11107596471035777 : Nat.Prime 11107596471035777 := by
  refine lucas_primality 11107596471035777 (3 : ZMod 11107596471035777) ?_ (fun q hq hd => ?_)
  · rw [show 11107596471035777 - 1 = 11107596471035776 from by norm_num]
    reduce_mod_char
  · have e : 11107596471035777 - 1 = [2 ^ 7, 43 ^ 2, 61 ^ 1, 15107 ^ 1, 50929 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11107596471035777 - 1) / 2 = 5553798235517888 from by norm_num]
      have h2 : (3 : ZMod 11107596471035777) ^ 5553798235517888 = ((11107596471035776 : ℕ) : ZMod 11107596471035777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11107596471035777 - 1) / 43 = 258316197000832 from by norm_num]
      have h2 : (3 : ZMod 11107596471035777) ^ 258316197000832 = ((11047738987028105 : ℕ) : ZMod 11107596471035777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11107596471035777 - 1) / 61 = 182091745426816 from by norm_num]
      have h2 : (3 : ZMod 11107596471035777) ^ 182091745426816 = ((5756949097073512 : ℕ) : ZMod 11107596471035777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11107596471035777 - 1) / 15107 = 735261565568 from by norm_num]
      have h2 : (3 : ZMod 11107596471035777) ^ 735261565568 = ((9744499351971270 : ℕ) : ZMod 11107596471035777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11107596471035777 - 1) / 50929 = 218099638144 from by norm_num]
      have h2 : (3 : ZMod 11107596471035777) ^ 218099638144 = ((4308708570058143 : ℕ) : ZMod 11107596471035777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_227020551154913939039124941009 : Nat.Prime 227020551154913939039124941009 := by
  refine lucas_primality 227020551154913939039124941009 (3 : ZMod 227020551154913939039124941009) ?_ (fun q hq hd => ?_)
  · rw [show 227020551154913939039124941009 - 1 = 227020551154913939039124941008 from by norm_num]
    reduce_mod_char
  · have e : 227020551154913939039124941009 - 1 = [2 ^ 4, 487 ^ 1, 2622986987 ^ 1, 11107596471035777 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (227020551154913939039124941009 - 1) / 2 = 113510275577456969519562470504 from by norm_num]
      have h2 : (3 : ZMod 227020551154913939039124941009) ^ 113510275577456969519562470504 = ((227020551154913939039124941008 : ℕ) : ZMod 227020551154913939039124941009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (227020551154913939039124941009 - 1) / 487 = 466161296005983447718942384 from by norm_num]
      have h2 : (3 : ZMod 227020551154913939039124941009) ^ 466161296005983447718942384 = ((227020551154913939039124938961 : ℕ) : ZMod 227020551154913939039124941009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2622986987).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (227020551154913939039124941009 - 1) / 2622986987 = 86550391702310774384 from by norm_num]
      have h2 : (3 : ZMod 227020551154913939039124941009) ^ 86550391702310774384 = ((97616390642481434880741425880 : ℕ) : ZMod 227020551154913939039124941009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_11107596471035777).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (227020551154913939039124941009 - 1) / 11107596471035777 = 20438314602704 from by norm_num]
      have h2 : (3 : ZMod 227020551154913939039124941009) ^ 20438314602704 = ((220504455203409252139402146772 : ℕ) : ZMod 227020551154913939039124941009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_100423529 : Nat.Prime 100423529 := by
  refine lucas_primality 100423529 (3 : ZMod 100423529) ?_ (fun q hq hd => ?_)
  · rw [show 100423529 - 1 = 100423528 from by norm_num]
    reduce_mod_char
  · have e : 100423529 - 1 = [2 ^ 3, 12552941 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (100423529 - 1) / 2 = 50211764 from by norm_num]
      have h2 : (3 : ZMod 100423529) ^ 50211764 = ((100423528 : ℕ) : ZMod 100423529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (100423529 - 1) / 12552941 = 8 from by norm_num]
      have h2 : (3 : ZMod 100423529) ^ 8 = ((6561 : ℕ) : ZMod 100423529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_25526656836511 : Nat.Prime 25526656836511 := by
  refine lucas_primality 25526656836511 (31 : ZMod 25526656836511) ?_ (fun q hq hd => ?_)
  · rw [show 25526656836511 - 1 = 25526656836510 from by norm_num]
    reduce_mod_char
  · have e : 25526656836511 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 37 ^ 1, 229 ^ 1, 100423529 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25526656836511 - 1) / 2 = 12763328418255 from by norm_num]
      have h2 : (31 : ZMod 25526656836511) ^ 12763328418255 = ((25526656836510 : ℕ) : ZMod 25526656836511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25526656836511 - 1) / 3 = 8508885612170 from by norm_num]
      have h2 : (31 : ZMod 25526656836511) ^ 8508885612170 = ((19931795788206 : ℕ) : ZMod 25526656836511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25526656836511 - 1) / 5 = 5105331367302 from by norm_num]
      have h2 : (31 : ZMod 25526656836511) ^ 5105331367302 = ((12721964710597 : ℕ) : ZMod 25526656836511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25526656836511 - 1) / 37 = 689909644230 from by norm_num]
      have h2 : (31 : ZMod 25526656836511) ^ 689909644230 = ((10445166535481 : ℕ) : ZMod 25526656836511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25526656836511 - 1) / 229 = 111470117190 from by norm_num]
      have h2 : (31 : ZMod 25526656836511) ^ 111470117190 = ((10463325310439 : ℕ) : ZMod 25526656836511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_100423529).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25526656836511 - 1) / 100423529 = 254190 from by norm_num]
      have h2 : (31 : ZMod 25526656836511) ^ 254190 = ((11378724536886 : ℕ) : ZMod 25526656836511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_189424531 : Nat.Prime 189424531 := by
  refine lucas_primality 189424531 (3 : ZMod 189424531) ?_ (fun q hq hd => ?_)
  · rw [show 189424531 - 1 = 189424530 from by norm_num]
    reduce_mod_char
  · have e : 189424531 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 1, 2104717 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (189424531 - 1) / 2 = 94712265 from by norm_num]
      have h2 : (3 : ZMod 189424531) ^ 94712265 = ((189424530 : ℕ) : ZMod 189424531) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (189424531 - 1) / 3 = 63141510 from by norm_num]
      have h2 : (3 : ZMod 189424531) ^ 63141510 = ((167302716 : ℕ) : ZMod 189424531) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (189424531 - 1) / 5 = 37884906 from by norm_num]
      have h2 : (3 : ZMod 189424531) ^ 37884906 = ((116515589 : ℕ) : ZMod 189424531) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (189424531 - 1) / 2104717 = 90 from by norm_num]
      have h2 : (3 : ZMod 189424531) ^ 90 = ((71533871 : ℕ) : ZMod 189424531) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6207820729933 : Nat.Prime 6207820729933 := by
  refine lucas_primality 6207820729933 (2 : ZMod 6207820729933) ?_ (fun q hq hd => ?_)
  · rw [show 6207820729933 - 1 = 6207820729932 from by norm_num]
    reduce_mod_char
  · have e : 6207820729933 - 1 = [2 ^ 2, 3 ^ 1, 2731 ^ 1, 189424531 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6207820729933 - 1) / 2 = 3103910364966 from by norm_num]
      have h2 : (2 : ZMod 6207820729933) ^ 3103910364966 = ((6207820729932 : ℕ) : ZMod 6207820729933) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6207820729933 - 1) / 3 = 2069273576644 from by norm_num]
      have h2 : (2 : ZMod 6207820729933) ^ 2069273576644 = ((3900625831824 : ℕ) : ZMod 6207820729933) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6207820729933 - 1) / 2731 = 2273094372 from by norm_num]
      have h2 : (2 : ZMod 6207820729933) ^ 2273094372 = ((735310845015 : ℕ) : ZMod 6207820729933) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_189424531).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6207820729933 - 1) / 189424531 = 32772 from by norm_num]
      have h2 : (2 : ZMod 6207820729933) ^ 32772 = ((5557757623094 : ℕ) : ZMod 6207820729933) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_81049307450005249 : Nat.Prime 81049307450005249 := by
  refine lucas_primality 81049307450005249 (14 : ZMod 81049307450005249) ?_ (fun q hq hd => ?_)
  · rw [show 81049307450005249 - 1 = 81049307450005248 from by norm_num]
    reduce_mod_char
  · have e : 81049307450005249 - 1 = [2 ^ 8, 3 ^ 1, 17 ^ 1, 6207820729933 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81049307450005249 - 1) / 2 = 40524653725002624 from by norm_num]
      have h2 : (14 : ZMod 81049307450005249) ^ 40524653725002624 = ((81049307450005248 : ℕ) : ZMod 81049307450005249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81049307450005249 - 1) / 3 = 27016435816668416 from by norm_num]
      have h2 : (14 : ZMod 81049307450005249) ^ 27016435816668416 = ((44049350366478107 : ℕ) : ZMod 81049307450005249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81049307450005249 - 1) / 17 = 4767606320588544 from by norm_num]
      have h2 : (14 : ZMod 81049307450005249) ^ 4767606320588544 = ((4985005215871308 : ℕ) : ZMod 81049307450005249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6207820729933).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81049307450005249 - 1) / 6207820729933 = 13056 from by norm_num]
      have h2 : (14 : ZMod 81049307450005249) ^ 13056 = ((66881150863476225 : ℕ) : ZMod 81049307450005249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_160801825980810414017 : Nat.Prime 160801825980810414017 := by
  refine lucas_primality 160801825980810414017 (3 : ZMod 160801825980810414017) ?_ (fun q hq hd => ?_)
  · rw [show 160801825980810414017 - 1 = 160801825980810414016 from by norm_num]
    reduce_mod_char
  · have e : 160801825980810414017 - 1 = [2 ^ 6, 31 ^ 1, 81049307450005249 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (160801825980810414017 - 1) / 2 = 80400912990405207008 from by norm_num]
      have h2 : (3 : ZMod 160801825980810414017) ^ 80400912990405207008 = ((160801825980810414016 : ℕ) : ZMod 160801825980810414017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (160801825980810414017 - 1) / 31 = 5187155676800335936 from by norm_num]
      have h2 : (3 : ZMod 160801825980810414017) ^ 5187155676800335936 = ((48009684975420478861 : ℕ) : ZMod 160801825980810414017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_81049307450005249).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (160801825980810414017 - 1) / 81049307450005249 = 1984 from by norm_num]
      have h2 : (3 : ZMod 160801825980810414017) ^ 1984 = ((22747843022592193175 : ℕ) : ZMod 160801825980810414017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3563269486977651154759062020950904488457 : Nat.Prime 3563269486977651154759062020950904488457 := by
  refine lucas_primality 3563269486977651154759062020950904488457 (3 : ZMod 3563269486977651154759062020950904488457) ?_ (fun q hq hd => ?_)
  · rw [show 3563269486977651154759062020950904488457 - 1 = 3563269486977651154759062020950904488456 from by norm_num]
    reduce_mod_char
  · have e : 3563269486977651154759062020950904488457 - 1 = [2 ^ 3, 13 ^ 1, 17 ^ 1, 491 ^ 1, 25526656836511 ^ 1, 160801825980810414017 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3563269486977651154759062020950904488457 - 1) / 2 = 1781634743488825577379531010475452244228 from by norm_num]
      have h2 : (3 : ZMod 3563269486977651154759062020950904488457) ^ 1781634743488825577379531010475452244228 = ((3563269486977651154759062020950904488456 : ℕ) : ZMod 3563269486977651154759062020950904488457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3563269486977651154759062020950904488457 - 1) / 13 = 274097652844434704212235540073146499112 from by norm_num]
      have h2 : (3 : ZMod 3563269486977651154759062020950904488457) ^ 274097652844434704212235540073146499112 = ((998298163017231999318160311480438467512 : ℕ) : ZMod 3563269486977651154759062020950904488457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3563269486977651154759062020950904488457 - 1) / 17 = 209604087469273597338768354173582616968 from by norm_num]
      have h2 : (3 : ZMod 3563269486977651154759062020950904488457) ^ 209604087469273597338768354173582616968 = ((1278640003636855156436479260517928524900 : ℕ) : ZMod 3563269486977651154759062020950904488457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3563269486977651154759062020950904488457 - 1) / 491 = 7257167997917823125782203708657646616 from by norm_num]
      have h2 : (3 : ZMod 3563269486977651154759062020950904488457) ^ 7257167997917823125782203708657646616 = ((178803131736785354043332915646786975987 : ℕ) : ZMod 3563269486977651154759062020950904488457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_25526656836511).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3563269486977651154759062020950904488457 - 1) / 25526656836511 = 139590135512029750683189496 from by norm_num]
      have h2 : (3 : ZMod 3563269486977651154759062020950904488457) ^ 139590135512029750683189496 = ((293227324440970660228977187827249530099 : ℕ) : ZMod 3563269486977651154759062020950904488457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_160801825980810414017).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3563269486977651154759062020950904488457 - 1) / 160801825980810414017 = 22159384479893160968 from by norm_num]
      have h2 : (3 : ZMod 3563269486977651154759062020950904488457) ^ 22159384479893160968 = ((161152572767803777041120673082284480001 : ℕ) : ZMod 3563269486977651154759062020950904488457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_88331359 : Nat.Prime 88331359 := by
  refine lucas_primality 88331359 (15 : ZMod 88331359) ?_ (fun q hq hd => ?_)
  · rw [show 88331359 - 1 = 88331358 from by norm_num]
    reduce_mod_char
  · have e : 88331359 - 1 = [2 ^ 1, 3 ^ 1, 37 ^ 1, 103 ^ 1, 3863 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88331359 - 1) / 2 = 44165679 from by norm_num]
      have h2 : (15 : ZMod 88331359) ^ 44165679 = ((88331358 : ℕ) : ZMod 88331359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88331359 - 1) / 3 = 29443786 from by norm_num]
      have h2 : (15 : ZMod 88331359) ^ 29443786 = ((46760582 : ℕ) : ZMod 88331359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88331359 - 1) / 37 = 2387334 from by norm_num]
      have h2 : (15 : ZMod 88331359) ^ 2387334 = ((28889418 : ℕ) : ZMod 88331359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88331359 - 1) / 103 = 857586 from by norm_num]
      have h2 : (15 : ZMod 88331359) ^ 857586 = ((22834783 : ℕ) : ZMod 88331359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88331359 - 1) / 3863 = 22866 from by norm_num]
      have h2 : (15 : ZMod 88331359) ^ 22866 = ((86970286 : ℕ) : ZMod 88331359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1943219363 : Nat.Prime 1943219363 := by
  refine lucas_primality 1943219363 (2 : ZMod 1943219363) ?_ (fun q hq hd => ?_)
  · rw [show 1943219363 - 1 = 1943219362 from by norm_num]
    reduce_mod_char
  · have e : 1943219363 - 1 = [2 ^ 1, 7 ^ 2, 19828769 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1943219363 - 1) / 2 = 971609681 from by norm_num]
      have h2 : (2 : ZMod 1943219363) ^ 971609681 = ((1943219362 : ℕ) : ZMod 1943219363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1943219363 - 1) / 7 = 277602766 from by norm_num]
      have h2 : (2 : ZMod 1943219363) ^ 277602766 = ((703175623 : ℕ) : ZMod 1943219363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1943219363 - 1) / 19828769 = 98 from by norm_num]
      have h2 : (2 : ZMod 1943219363) ^ 98 = ((344949811 : ℕ) : ZMod 1943219363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_90268296000189649868678102552775904610963 : Nat.Prime 90268296000189649868678102552775904610963 := by
  refine lucas_primality 90268296000189649868678102552775904610963 (5 : ZMod 90268296000189649868678102552775904610963) ?_ (fun q hq hd => ?_)
  · rw [show 90268296000189649868678102552775904610963 - 1 = 90268296000189649868678102552775904610962 from by norm_num]
    reduce_mod_char
  · have e : 90268296000189649868678102552775904610963 - 1 = [2 ^ 1, 521 ^ 1, 1489 ^ 1, 1847 ^ 1, 4742329 ^ 1, 38697019 ^ 1, 88331359 ^ 1, 1943219363 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (90268296000189649868678102552775904610963 - 1) / 2 = 45134148000094824934339051276387952305481 from by norm_num]
      have h2 : (5 : ZMod 90268296000189649868678102552775904610963) ^ 45134148000094824934339051276387952305481 = ((90268296000189649868678102552775904610962 : ℕ) : ZMod 90268296000189649868678102552775904610963) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (90268296000189649868678102552775904610963 - 1) / 521 = 173259685221093377866944534650241659522 from by norm_num]
      have h2 : (5 : ZMod 90268296000189649868678102552775904610963) ^ 173259685221093377866944534650241659522 = ((59347887695188704294041000552166563937275 : ℕ) : ZMod 90268296000189649868678102552775904610963) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (90268296000189649868678102552775904610963 - 1) / 1489 = 60623435863122666130744192446457961458 from by norm_num]
      have h2 : (5 : ZMod 90268296000189649868678102552775904610963) ^ 60623435863122666130744192446457961458 = ((80983034079311590249204270698520270275199 : ℕ) : ZMod 90268296000189649868678102552775904610963) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (90268296000189649868678102552775904610963 - 1) / 1847 = 48872926908602950659814890391324258046 from by norm_num]
      have h2 : (5 : ZMod 90268296000189649868678102552775904610963) ^ 48872926908602950659814890391324258046 = ((82736292031485375019503394414762086684590 : ℕ) : ZMod 90268296000189649868678102552775904610963) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (90268296000189649868678102552775904610963 - 1) / 4742329 = 19034591653212936063414854294751778 from by norm_num]
      have h2 : (5 : ZMod 90268296000189649868678102552775904610963) ^ 19034591653212936063414854294751778 = ((59466396215515655205843192587779206093382 : ℕ) : ZMod 90268296000189649868678102552775904610963) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (90268296000189649868678102552775904610963 - 1) / 38697019 = 2332693792257994081370404850894998 from by norm_num]
      have h2 : (5 : ZMod 90268296000189649868678102552775904610963) ^ 2332693792257994081370404850894998 = ((3938103408181121077284127037429357086544 : ℕ) : ZMod 90268296000189649868678102552775904610963) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_88331359).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (90268296000189649868678102552775904610963 - 1) / 88331359 = 1021928078794640189659915710713518 from by norm_num]
      have h2 : (5 : ZMod 90268296000189649868678102552775904610963) ^ 1021928078794640189659915710713518 = ((9077449111521971793950034124009523894287 : ℕ) : ZMod 90268296000189649868678102552775904610963) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1943219363).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (90268296000189649868678102552775904610963 - 1) / 1943219363 = 46452962397837968573534691848774 from by norm_num]
      have h2 : (5 : ZMod 90268296000189649868678102552775904610963) ^ 46452962397837968573534691848774 = ((89160768226770758419841692350667252295413 : ℕ) : ZMod 90268296000189649868678102552775904610963) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_129175771 : Nat.Prime 129175771 := by
  refine lucas_primality 129175771 (10 : ZMod 129175771) ?_ (fun q hq hd => ?_)
  · rw [show 129175771 - 1 = 129175770 from by norm_num]
    reduce_mod_char
  · have e : 129175771 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 523 ^ 1, 8233 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129175771 - 1) / 2 = 64587885 from by norm_num]
      have h2 : (10 : ZMod 129175771) ^ 64587885 = ((129175770 : ℕ) : ZMod 129175771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129175771 - 1) / 3 = 43058590 from by norm_num]
      have h2 : (10 : ZMod 129175771) ^ 43058590 = ((82954762 : ℕ) : ZMod 129175771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129175771 - 1) / 5 = 25835154 from by norm_num]
      have h2 : (10 : ZMod 129175771) ^ 25835154 = ((63172287 : ℕ) : ZMod 129175771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129175771 - 1) / 523 = 246990 from by norm_num]
      have h2 : (10 : ZMod 129175771) ^ 246990 = ((37208342 : ℕ) : ZMod 129175771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129175771 - 1) / 8233 = 15690 from by norm_num]
      have h2 : (10 : ZMod 129175771) ^ 15690 = ((57613618 : ℕ) : ZMod 129175771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_58421933 : Nat.Prime 58421933 := by
  refine lucas_primality 58421933 (3 : ZMod 58421933) ?_ (fun q hq hd => ?_)
  · rw [show 58421933 - 1 = 58421932 from by norm_num]
    reduce_mod_char
  · have e : 58421933 - 1 = [2 ^ 2, 23 ^ 1, 635021 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58421933 - 1) / 2 = 29210966 from by norm_num]
      have h2 : (3 : ZMod 58421933) ^ 29210966 = ((58421932 : ℕ) : ZMod 58421933) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58421933 - 1) / 23 = 2540084 from by norm_num]
      have h2 : (3 : ZMod 58421933) ^ 2540084 = ((12714040 : ℕ) : ZMod 58421933) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58421933 - 1) / 635021 = 92 from by norm_num]
      have h2 : (3 : ZMod 58421933) ^ 92 = ((12897645 : ℕ) : ZMod 58421933) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1533926272849 : Nat.Prime 1533926272849 := by
  refine lucas_primality 1533926272849 (7 : ZMod 1533926272849) ?_ (fun q hq hd => ?_)
  · rw [show 1533926272849 - 1 = 1533926272848 from by norm_num]
    reduce_mod_char
  · have e : 1533926272849 - 1 = [2 ^ 4, 3 ^ 1, 547 ^ 1, 58421933 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1533926272849 - 1) / 2 = 766963136424 from by norm_num]
      have h2 : (7 : ZMod 1533926272849) ^ 766963136424 = ((1533926272848 : ℕ) : ZMod 1533926272849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1533926272849 - 1) / 3 = 511308757616 from by norm_num]
      have h2 : (7 : ZMod 1533926272849) ^ 511308757616 = ((257640996136 : ℕ) : ZMod 1533926272849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1533926272849 - 1) / 547 = 2804252784 from by norm_num]
      have h2 : (7 : ZMod 1533926272849) ^ 2804252784 = ((1442098404641 : ℕ) : ZMod 1533926272849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_58421933).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1533926272849 - 1) / 58421933 = 26256 from by norm_num]
      have h2 : (7 : ZMod 1533926272849) ^ 26256 = ((483124433242 : ℕ) : ZMod 1533926272849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_332781217 : Nat.Prime 332781217 := by
  refine lucas_primality 332781217 (5 : ZMod 332781217) ?_ (fun q hq hd => ?_)
  · rw [show 332781217 - 1 = 332781216 from by norm_num]
    reduce_mod_char
  · have e : 332781217 - 1 = [2 ^ 5, 3 ^ 1, 3466471 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (332781217 - 1) / 2 = 166390608 from by norm_num]
      have h2 : (5 : ZMod 332781217) ^ 166390608 = ((332781216 : ℕ) : ZMod 332781217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (332781217 - 1) / 3 = 110927072 from by norm_num]
      have h2 : (5 : ZMod 332781217) ^ 110927072 = ((229382491 : ℕ) : ZMod 332781217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (332781217 - 1) / 3466471 = 96 from by norm_num]
      have h2 : (5 : ZMod 332781217) ^ 96 = ((252793911 : ℕ) : ZMod 332781217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_34598597569057 : Nat.Prime 34598597569057 := by
  refine lucas_primality 34598597569057 (5 : ZMod 34598597569057) ?_ (fun q hq hd => ?_)
  · rw [show 34598597569057 - 1 = 34598597569056 from by norm_num]
    reduce_mod_char
  · have e : 34598597569057 - 1 = [2 ^ 5, 3 ^ 2, 19 ^ 2, 332781217 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34598597569057 - 1) / 2 = 17299298784528 from by norm_num]
      have h2 : (5 : ZMod 34598597569057) ^ 17299298784528 = ((34598597569056 : ℕ) : ZMod 34598597569057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34598597569057 - 1) / 3 = 11532865856352 from by norm_num]
      have h2 : (5 : ZMod 34598597569057) ^ 11532865856352 = ((6106559209547 : ℕ) : ZMod 34598597569057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34598597569057 - 1) / 19 = 1820978819424 from by norm_num]
      have h2 : (5 : ZMod 34598597569057) ^ 1820978819424 = ((29401464061680 : ℕ) : ZMod 34598597569057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_332781217).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34598597569057 - 1) / 332781217 = 103968 from by norm_num]
      have h2 : (5 : ZMod 34598597569057) ^ 103968 = ((12643409826686 : ℕ) : ZMod 34598597569057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_74906924194076922022321 : Nat.Prime 74906924194076922022321 := by
  refine lucas_primality 74906924194076922022321 (19 : ZMod 74906924194076922022321) ?_ (fun q hq hd => ?_)
  · rw [show 74906924194076922022321 - 1 = 74906924194076922022320 from by norm_num]
    reduce_mod_char
  · have e : 74906924194076922022321 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 1, 7 ^ 2, 109 ^ 1, 563 ^ 1, 34598597569057 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74906924194076922022321 - 1) / 2 = 37453462097038461011160 from by norm_num]
      have h2 : (19 : ZMod 74906924194076922022321) ^ 37453462097038461011160 = ((74906924194076922022320 : ℕ) : ZMod 74906924194076922022321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74906924194076922022321 - 1) / 3 = 24968974731358974007440 from by norm_num]
      have h2 : (19 : ZMod 74906924194076922022321) ^ 24968974731358974007440 = ((51307005567160672823577 : ℕ) : ZMod 74906924194076922022321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74906924194076922022321 - 1) / 5 = 14981384838815384404464 from by norm_num]
      have h2 : (19 : ZMod 74906924194076922022321) ^ 14981384838815384404464 = ((22890246513722193150310 : ℕ) : ZMod 74906924194076922022321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74906924194076922022321 - 1) / 7 = 10700989170582417431760 from by norm_num]
      have h2 : (19 : ZMod 74906924194076922022321) ^ 10700989170582417431760 = ((25740687939208719162501 : ℕ) : ZMod 74906924194076922022321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74906924194076922022321 - 1) / 109 = 687219488019054330480 from by norm_num]
      have h2 : (19 : ZMod 74906924194076922022321) ^ 687219488019054330480 = ((29325524688098728029047 : ℕ) : ZMod 74906924194076922022321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74906924194076922022321 - 1) / 563 = 133049598923760074640 from by norm_num]
      have h2 : (19 : ZMod 74906924194076922022321) ^ 133049598923760074640 = ((62199162663003280394836 : ℕ) : ZMod 74906924194076922022321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_34598597569057).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74906924194076922022321 - 1) / 34598597569057 = 2165027760 from by norm_num]
      have h2 : (19 : ZMod 74906924194076922022321) ^ 2165027760 = ((8843761633513109345624 : ℕ) : ZMod 74906924194076922022321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2318527093 : Nat.Prime 2318527093 := by
  refine lucas_primality 2318527093 (5 : ZMod 2318527093) ?_ (fun q hq hd => ?_)
  · rw [show 2318527093 - 1 = 2318527092 from by norm_num]
    reduce_mod_char
  · have e : 2318527093 - 1 = [2 ^ 2, 3 ^ 1, 7 ^ 1, 27601513 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2318527093 - 1) / 2 = 1159263546 from by norm_num]
      have h2 : (5 : ZMod 2318527093) ^ 1159263546 = ((2318527092 : ℕ) : ZMod 2318527093) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2318527093 - 1) / 3 = 772842364 from by norm_num]
      have h2 : (5 : ZMod 2318527093) ^ 772842364 = ((794990648 : ℕ) : ZMod 2318527093) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2318527093 - 1) / 7 = 331218156 from by norm_num]
      have h2 : (5 : ZMod 2318527093) ^ 331218156 = ((2004652146 : ℕ) : ZMod 2318527093) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2318527093 - 1) / 27601513 = 84 from by norm_num]
      have h2 : (5 : ZMod 2318527093) ^ 84 = ((139060304 : ℕ) : ZMod 2318527093) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2058017388830521 : Nat.Prime 2058017388830521 := by
  refine lucas_primality 2058017388830521 (7 : ZMod 2058017388830521) ?_ (fun q hq hd => ?_)
  · rw [show 2058017388830521 - 1 = 2058017388830520 from by norm_num]
    reduce_mod_char
  · have e : 2058017388830521 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 13 ^ 1, 569 ^ 1, 2318527093 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2058017388830521 - 1) / 2 = 1029008694415260 from by norm_num]
      have h2 : (7 : ZMod 2058017388830521) ^ 1029008694415260 = ((2058017388830520 : ℕ) : ZMod 2058017388830521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2058017388830521 - 1) / 3 = 686005796276840 from by norm_num]
      have h2 : (7 : ZMod 2058017388830521) ^ 686005796276840 = ((1135262034489874 : ℕ) : ZMod 2058017388830521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2058017388830521 - 1) / 5 = 411603477766104 from by norm_num]
      have h2 : (7 : ZMod 2058017388830521) ^ 411603477766104 = ((1883269546275262 : ℕ) : ZMod 2058017388830521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2058017388830521 - 1) / 13 = 158309029910040 from by norm_num]
      have h2 : (7 : ZMod 2058017388830521) ^ 158309029910040 = ((1111609288842446 : ℕ) : ZMod 2058017388830521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2058017388830521 - 1) / 569 = 3616902265080 from by norm_num]
      have h2 : (7 : ZMod 2058017388830521) ^ 3616902265080 = ((1487447391896269 : ℕ) : ZMod 2058017388830521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2318527093).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2058017388830521 - 1) / 2318527093 = 887640 from by norm_num]
      have h2 : (7 : ZMod 2058017388830521) ^ 887640 = ((1776819975475389 : ℕ) : ZMod 2058017388830521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_73205584889 : Nat.Prime 73205584889 := by
  refine lucas_primality 73205584889 (3 : ZMod 73205584889) ?_ (fun q hq hd => ?_)
  · rw [show 73205584889 - 1 = 73205584888 from by norm_num]
    reduce_mod_char
  · have e : 73205584889 - 1 = [2 ^ 3, 571 ^ 1, 16025741 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (73205584889 - 1) / 2 = 36602792444 from by norm_num]
      have h2 : (3 : ZMod 73205584889) ^ 36602792444 = ((73205584888 : ℕ) : ZMod 73205584889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (73205584889 - 1) / 571 = 128205928 from by norm_num]
      have h2 : (3 : ZMod 73205584889) ^ 128205928 = ((73205584377 : ℕ) : ZMod 73205584889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (73205584889 - 1) / 16025741 = 4568 from by norm_num]
      have h2 : (3 : ZMod 73205584889) ^ 4568 = ((70954170616 : ℕ) : ZMod 73205584889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_13119770765051463547 : Nat.Prime 13119770765051463547 := by
  refine lucas_primality 13119770765051463547 (11 : ZMod 13119770765051463547) ?_ (fun q hq hd => ?_)
  · rw [show 13119770765051463547 - 1 = 13119770765051463546 from by norm_num]
    reduce_mod_char
  · have e : 13119770765051463547 - 1 = [2 ^ 1, 3 ^ 6, 11 ^ 1, 73 ^ 1, 587 ^ 1, 5387 ^ 1, 3543791 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13119770765051463547 - 1) / 2 = 6559885382525731773 from by norm_num]
      have h2 : (11 : ZMod 13119770765051463547) ^ 6559885382525731773 = ((13119770765051463546 : ℕ) : ZMod 13119770765051463547) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13119770765051463547 - 1) / 3 = 4373256921683821182 from by norm_num]
      have h2 : (11 : ZMod 13119770765051463547) ^ 4373256921683821182 = ((12111068943706966634 : ℕ) : ZMod 13119770765051463547) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13119770765051463547 - 1) / 11 = 1192706433186496686 from by norm_num]
      have h2 : (11 : ZMod 13119770765051463547) ^ 1192706433186496686 = ((3907293564301290298 : ℕ) : ZMod 13119770765051463547) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13119770765051463547 - 1) / 73 = 179722887192485802 from by norm_num]
      have h2 : (11 : ZMod 13119770765051463547) ^ 179722887192485802 = ((9674430476895619127 : ℕ) : ZMod 13119770765051463547) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13119770765051463547 - 1) / 587 = 22350546448128558 from by norm_num]
      have h2 : (11 : ZMod 13119770765051463547) ^ 22350546448128558 = ((5919568897858987316 : ℕ) : ZMod 13119770765051463547) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13119770765051463547 - 1) / 5387 = 2435450299805358 from by norm_num]
      have h2 : (11 : ZMod 13119770765051463547) ^ 2435450299805358 = ((10883718494945262238 : ℕ) : ZMod 13119770765051463547) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13119770765051463547 - 1) / 3543791 = 3702185248806 from by norm_num]
      have h2 : (11 : ZMod 13119770765051463547) ^ 3702185248806 = ((10462141958465466286 : ℕ) : ZMod 13119770765051463547) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_86124003836379527 : Nat.Prime 86124003836379527 := by
  refine lucas_primality 86124003836379527 (5 : ZMod 86124003836379527) ?_ (fun q hq hd => ?_)
  · rw [show 86124003836379527 - 1 = 86124003836379526 from by norm_num]
    reduce_mod_char
  · have e : 86124003836379527 - 1 = [2 ^ 1, 4493 ^ 1, 1117889 ^ 1, 8573519 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86124003836379527 - 1) / 2 = 43062001918189763 from by norm_num]
      have h2 : (5 : ZMod 86124003836379527) ^ 43062001918189763 = ((86124003836379526 : ℕ) : ZMod 86124003836379527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86124003836379527 - 1) / 4493 = 19168485162782 from by norm_num]
      have h2 : (5 : ZMod 86124003836379527) ^ 19168485162782 = ((74112066823082037 : ℕ) : ZMod 86124003836379527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86124003836379527 - 1) / 1117889 = 77041641734 from by norm_num]
      have h2 : (5 : ZMod 86124003836379527) ^ 77041641734 = ((65358735249621522 : ℕ) : ZMod 86124003836379527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86124003836379527 - 1) / 8573519 = 10045350554 from by norm_num]
      have h2 : (5 : ZMod 86124003836379527) ^ 10045350554 = ((47568780838102336 : ℕ) : ZMod 86124003836379527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6975729612775483517844546731 : Nat.Prime 6975729612775483517844546731 := by
  refine lucas_primality 6975729612775483517844546731 (6 : ZMod 6975729612775483517844546731) ?_ (fun q hq hd => ?_)
  · rw [show 6975729612775483517844546731 - 1 = 6975729612775483517844546730 from by norm_num]
    reduce_mod_char
  · have e : 6975729612775483517844546731 - 1 = [2 ^ 1, 5 ^ 1, 7 ^ 1, 593 ^ 1, 1951249 ^ 1, 86124003836379527 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6975729612775483517844546731 - 1) / 2 = 3487864806387741758922273365 from by norm_num]
      have h2 : (6 : ZMod 6975729612775483517844546731) ^ 3487864806387741758922273365 = ((6975729612775483517844546730 : ℕ) : ZMod 6975729612775483517844546731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6975729612775483517844546731 - 1) / 5 = 1395145922555096703568909346 from by norm_num]
      have h2 : (6 : ZMod 6975729612775483517844546731) ^ 1395145922555096703568909346 = ((4242907130769565877689288674 : ℕ) : ZMod 6975729612775483517844546731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6975729612775483517844546731 - 1) / 7 = 996532801825069073977792390 from by norm_num]
      have h2 : (6 : ZMod 6975729612775483517844546731) ^ 996532801825069073977792390 = ((2670069566498494140725596495 : ℕ) : ZMod 6975729612775483517844546731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6975729612775483517844546731 - 1) / 593 = 11763456345321220097545610 from by norm_num]
      have h2 : (6 : ZMod 6975729612775483517844546731) ^ 11763456345321220097545610 = ((4450755757207740237015122914 : ℕ) : ZMod 6975729612775483517844546731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6975729612775483517844546731 - 1) / 1951249 = 3575007399248114165770 from by norm_num]
      have h2 : (6 : ZMod 6975729612775483517844546731) ^ 3575007399248114165770 = ((5245206124047166303483981197 : ℕ) : ZMod 6975729612775483517844546731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_86124003836379527).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6975729612775483517844546731 - 1) / 86124003836379527 = 80996345990 from by norm_num]
      have h2 : (6 : ZMod 6975729612775483517844546731) ^ 80996345990 = ((3507625632960622547798297944 : ℕ) : ZMod 6975729612775483517844546731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_366994123 : Nat.Prime 366994123 := by
  refine lucas_primality 366994123 (3 : ZMod 366994123) ?_ (fun q hq hd => ?_)
  · rw [show 366994123 - 1 = 366994122 from by norm_num]
    reduce_mod_char
  · have e : 366994123 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 599 ^ 1, 9283 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (366994123 - 1) / 2 = 183497061 from by norm_num]
      have h2 : (3 : ZMod 366994123) ^ 183497061 = ((366994122 : ℕ) : ZMod 366994123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (366994123 - 1) / 3 = 122331374 from by norm_num]
      have h2 : (3 : ZMod 366994123) ^ 122331374 = ((178687973 : ℕ) : ZMod 366994123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (366994123 - 1) / 11 = 33363102 from by norm_num]
      have h2 : (3 : ZMod 366994123) ^ 33363102 = ((31745232 : ℕ) : ZMod 366994123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (366994123 - 1) / 599 = 612678 from by norm_num]
      have h2 : (3 : ZMod 366994123) ^ 612678 = ((201979991 : ℕ) : ZMod 366994123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (366994123 - 1) / 9283 = 39534 from by norm_num]
      have h2 : (3 : ZMod 366994123) ^ 39534 = ((304858254 : ℕ) : ZMod 366994123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2655094158137 : Nat.Prime 2655094158137 := by
  refine lucas_primality 2655094158137 (3 : ZMod 2655094158137) ?_ (fun q hq hd => ?_)
  · rw [show 2655094158137 - 1 = 2655094158136 from by norm_num]
    reduce_mod_char
  · have e : 2655094158137 - 1 = [2 ^ 3, 7 ^ 2, 25121 ^ 1, 269623 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2655094158137 - 1) / 2 = 1327547079068 from by norm_num]
      have h2 : (3 : ZMod 2655094158137) ^ 1327547079068 = ((2655094158136 : ℕ) : ZMod 2655094158137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2655094158137 - 1) / 7 = 379299165448 from by norm_num]
      have h2 : (3 : ZMod 2655094158137) ^ 379299165448 = ((1462482469513 : ℕ) : ZMod 2655094158137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2655094158137 - 1) / 25121 = 105692216 from by norm_num]
      have h2 : (3 : ZMod 2655094158137) ^ 105692216 = ((432589312692 : ℕ) : ZMod 2655094158137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2655094158137 - 1) / 269623 = 9847432 from by norm_num]
      have h2 : (3 : ZMod 2655094158137) ^ 9847432 = ((51720311101 : ℕ) : ZMod 2655094158137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_21240753265097 : Nat.Prime 21240753265097 := by
  refine lucas_primality 21240753265097 (3 : ZMod 21240753265097) ?_ (fun q hq hd => ?_)
  · rw [show 21240753265097 - 1 = 21240753265096 from by norm_num]
    reduce_mod_char
  · have e : 21240753265097 - 1 = [2 ^ 3, 2655094158137 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21240753265097 - 1) / 2 = 10620376632548 from by norm_num]
      have h2 : (3 : ZMod 21240753265097) ^ 10620376632548 = ((21240753265096 : ℕ) : ZMod 21240753265097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2655094158137).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21240753265097 - 1) / 2655094158137 = 8 from by norm_num]
      have h2 : (3 : ZMod 21240753265097) ^ 8 = ((6561 : ℕ) : ZMod 21240753265097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9293424294571360217 : Nat.Prime 9293424294571360217 := by
  refine lucas_primality 9293424294571360217 (3 : ZMod 9293424294571360217) ?_ (fun q hq hd => ?_)
  · rw [show 9293424294571360217 - 1 = 9293424294571360216 from by norm_num]
    reduce_mod_char
  · have e : 9293424294571360217 - 1 = [2 ^ 3, 7 ^ 1, 13 ^ 1, 601 ^ 1, 21240753265097 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9293424294571360217 - 1) / 2 = 4646712147285680108 from by norm_num]
      have h2 : (3 : ZMod 9293424294571360217) ^ 4646712147285680108 = ((9293424294571360216 : ℕ) : ZMod 9293424294571360217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9293424294571360217 - 1) / 7 = 1327632042081622888 from by norm_num]
      have h2 : (3 : ZMod 9293424294571360217) ^ 1327632042081622888 = ((4776803137523851738 : ℕ) : ZMod 9293424294571360217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9293424294571360217 - 1) / 13 = 714878791890104632 from by norm_num]
      have h2 : (3 : ZMod 9293424294571360217) ^ 714878791890104632 = ((5622510938907186140 : ℕ) : ZMod 9293424294571360217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9293424294571360217 - 1) / 601 = 15463268376990616 from by norm_num]
      have h2 : (3 : ZMod 9293424294571360217) ^ 15463268376990616 = ((6970068220928520163 : ℕ) : ZMod 9293424294571360217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_21240753265097).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9293424294571360217 - 1) / 21240753265097 = 437528 from by norm_num]
      have h2 : (3 : ZMod 9293424294571360217) ^ 437528 = ((3517700697625967342 : ℕ) : ZMod 9293424294571360217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1081756861144651 : Nat.Prime 1081756861144651 := by
  refine lucas_primality 1081756861144651 (14 : ZMod 1081756861144651) ?_ (fun q hq hd => ?_)
  · rw [show 1081756861144651 - 1 = 1081756861144650 from by norm_num]
    reduce_mod_char
  · have e : 1081756861144651 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 2, 53 ^ 1, 643 ^ 1, 5507 ^ 1, 12809 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1081756861144651 - 1) / 2 = 540878430572325 from by norm_num]
      have h2 : (14 : ZMod 1081756861144651) ^ 540878430572325 = ((1081756861144650 : ℕ) : ZMod 1081756861144651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1081756861144651 - 1) / 3 = 360585620381550 from by norm_num]
      have h2 : (14 : ZMod 1081756861144651) ^ 360585620381550 = ((665142762644795 : ℕ) : ZMod 1081756861144651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1081756861144651 - 1) / 5 = 216351372228930 from by norm_num]
      have h2 : (14 : ZMod 1081756861144651) ^ 216351372228930 = ((319686897139759 : ℕ) : ZMod 1081756861144651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1081756861144651 - 1) / 53 = 20410506814050 from by norm_num]
      have h2 : (14 : ZMod 1081756861144651) ^ 20410506814050 = ((523404458132262 : ℕ) : ZMod 1081756861144651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1081756861144651 - 1) / 643 = 1682359037550 from by norm_num]
      have h2 : (14 : ZMod 1081756861144651) ^ 1682359037550 = ((895274284803117 : ℕ) : ZMod 1081756861144651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1081756861144651 - 1) / 5507 = 196433059950 from by norm_num]
      have h2 : (14 : ZMod 1081756861144651) ^ 196433059950 = ((618137396589073 : ℕ) : ZMod 1081756861144651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1081756861144651 - 1) / 12809 = 84452873850 from by norm_num]
      have h2 : (14 : ZMod 1081756861144651) ^ 84452873850 = ((865264935175602 : ℕ) : ZMod 1081756861144651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_12550478467 : Nat.Prime 12550478467 := by
  refine lucas_primality 12550478467 (3 : ZMod 12550478467) ?_ (fun q hq hd => ?_)
  · rw [show 12550478467 - 1 = 12550478466 from by norm_num]
    reduce_mod_char
  · have e : 12550478467 - 1 = [2 ^ 1, 3 ^ 1, 59 ^ 1, 653 ^ 1, 54293 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12550478467 - 1) / 2 = 6275239233 from by norm_num]
      have h2 : (3 : ZMod 12550478467) ^ 6275239233 = ((12550478466 : ℕ) : ZMod 12550478467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12550478467 - 1) / 3 = 4183492822 from by norm_num]
      have h2 : (3 : ZMod 12550478467) ^ 4183492822 = ((5877562385 : ℕ) : ZMod 12550478467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12550478467 - 1) / 59 = 212719974 from by norm_num]
      have h2 : (3 : ZMod 12550478467) ^ 212719974 = ((7802529451 : ℕ) : ZMod 12550478467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12550478467 - 1) / 653 = 19219722 from by norm_num]
      have h2 : (3 : ZMod 12550478467) ^ 19219722 = ((8685690442 : ℕ) : ZMod 12550478467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12550478467 - 1) / 54293 = 231162 from by norm_num]
      have h2 : (3 : ZMod 12550478467) ^ 231162 = ((215274054 : ℕ) : ZMod 12550478467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4061132942857 : Nat.Prime 4061132942857 := by
  refine lucas_primality 4061132942857 (5 : ZMod 4061132942857) ?_ (fun q hq hd => ?_)
  · rw [show 4061132942857 - 1 = 4061132942856 from by norm_num]
    reduce_mod_char
  · have e : 4061132942857 - 1 = [2 ^ 3, 3 ^ 1, 11 ^ 1, 157 ^ 1, 673 ^ 1, 145589 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4061132942857 - 1) / 2 = 2030566471428 from by norm_num]
      have h2 : (5 : ZMod 4061132942857) ^ 2030566471428 = ((4061132942856 : ℕ) : ZMod 4061132942857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4061132942857 - 1) / 3 = 1353710980952 from by norm_num]
      have h2 : (5 : ZMod 4061132942857) ^ 1353710980952 = ((1772731149220 : ℕ) : ZMod 4061132942857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4061132942857 - 1) / 11 = 369193903896 from by norm_num]
      have h2 : (5 : ZMod 4061132942857) ^ 369193903896 = ((1299956835183 : ℕ) : ZMod 4061132942857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4061132942857 - 1) / 157 = 25867088808 from by norm_num]
      have h2 : (5 : ZMod 4061132942857) ^ 25867088808 = ((2180933919989 : ℕ) : ZMod 4061132942857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4061132942857 - 1) / 673 = 6034372872 from by norm_num]
      have h2 : (5 : ZMod 4061132942857) ^ 6034372872 = ((16384 : ℕ) : ZMod 4061132942857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4061132942857 - 1) / 145589 = 27894504 from by norm_num]
      have h2 : (5 : ZMod 4061132942857) ^ 27894504 = ((3900506569430 : ℕ) : ZMod 4061132942857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4668478921 : Nat.Prime 4668478921 := by
  refine lucas_primality 4668478921 (47 : ZMod 4668478921) ?_ (fun q hq hd => ?_)
  · rw [show 4668478921 - 1 = 4668478920 from by norm_num]
    reduce_mod_char
  · have e : 4668478921 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 7 ^ 2, 383 ^ 1, 691 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4668478921 - 1) / 2 = 2334239460 from by norm_num]
      have h2 : (47 : ZMod 4668478921) ^ 2334239460 = ((4668478920 : ℕ) : ZMod 4668478921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4668478921 - 1) / 3 = 1556159640 from by norm_num]
      have h2 : (47 : ZMod 4668478921) ^ 1556159640 = ((1742284526 : ℕ) : ZMod 4668478921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4668478921 - 1) / 5 = 933695784 from by norm_num]
      have h2 : (47 : ZMod 4668478921) ^ 933695784 = ((1380057179 : ℕ) : ZMod 4668478921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4668478921 - 1) / 7 = 666925560 from by norm_num]
      have h2 : (47 : ZMod 4668478921) ^ 666925560 = ((3694177442 : ℕ) : ZMod 4668478921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4668478921 - 1) / 383 = 12189240 from by norm_num]
      have h2 : (47 : ZMod 4668478921) ^ 12189240 = ((2282482228 : ℕ) : ZMod 4668478921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4668478921 - 1) / 691 = 6756120 from by norm_num]
      have h2 : (47 : ZMod 4668478921) ^ 6756120 = ((2826578481 : ℕ) : ZMod 4668478921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5045586197318561 : Nat.Prime 5045586197318561 := by
  refine lucas_primality 5045586197318561 (3 : ZMod 5045586197318561) ?_ (fun q hq hd => ?_)
  · rw [show 5045586197318561 - 1 = 5045586197318560 from by norm_num]
    reduce_mod_char
  · have e : 5045586197318561 - 1 = [2 ^ 5, 5 ^ 1, 709 ^ 1, 907 ^ 1, 5683 ^ 1, 8629 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5045586197318561 - 1) / 2 = 2522793098659280 from by norm_num]
      have h2 : (3 : ZMod 5045586197318561) ^ 2522793098659280 = ((5045586197318560 : ℕ) : ZMod 5045586197318561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5045586197318561 - 1) / 5 = 1009117239463712 from by norm_num]
      have h2 : (3 : ZMod 5045586197318561) ^ 1009117239463712 = ((4067254286635776 : ℕ) : ZMod 5045586197318561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5045586197318561 - 1) / 709 = 7116482647840 from by norm_num]
      have h2 : (3 : ZMod 5045586197318561) ^ 7116482647840 = ((17179869184 : ℕ) : ZMod 5045586197318561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5045586197318561 - 1) / 907 = 5562939578080 from by norm_num]
      have h2 : (3 : ZMod 5045586197318561) ^ 5562939578080 = ((4038868965445578 : ℕ) : ZMod 5045586197318561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5045586197318561 - 1) / 5683 = 887838500320 from by norm_num]
      have h2 : (3 : ZMod 5045586197318561) ^ 887838500320 = ((4288006615212641 : ℕ) : ZMod 5045586197318561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5045586197318561 - 1) / 8629 = 584724324640 from by norm_num]
      have h2 : (3 : ZMod 5045586197318561) ^ 584724324640 = ((3119735886840291 : ℕ) : ZMod 5045586197318561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3511781227 : Nat.Prime 3511781227 := by
  refine lucas_primality 3511781227 (2 : ZMod 3511781227) ?_ (fun q hq hd => ?_)
  · rw [show 3511781227 - 1 = 3511781226 from by norm_num]
    reduce_mod_char
  · have e : 3511781227 - 1 = [2 ^ 1, 3 ^ 2, 3061 ^ 1, 63737 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3511781227 - 1) / 2 = 1755890613 from by norm_num]
      have h2 : (2 : ZMod 3511781227) ^ 1755890613 = ((3511781226 : ℕ) : ZMod 3511781227) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3511781227 - 1) / 3 = 1170593742 from by norm_num]
      have h2 : (2 : ZMod 3511781227) ^ 1170593742 = ((3398701968 : ℕ) : ZMod 3511781227) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3511781227 - 1) / 3061 = 1147266 from by norm_num]
      have h2 : (2 : ZMod 3511781227) ^ 1147266 = ((2132330767 : ℕ) : ZMod 3511781227) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3511781227 - 1) / 63737 = 55098 from by norm_num]
      have h2 : (2 : ZMod 3511781227) ^ 55098 = ((1576839714 : ℕ) : ZMod 3511781227) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_981270131 : Nat.Prime 981270131 := by
  refine lucas_primality 981270131 (2 : ZMod 981270131) ?_ (fun q hq hd => ?_)
  · rw [show 981270131 - 1 = 981270130 from by norm_num]
    reduce_mod_char
  · have e : 981270131 - 1 = [2 ^ 1, 5 ^ 1, 607 ^ 1, 161659 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (981270131 - 1) / 2 = 490635065 from by norm_num]
      have h2 : (2 : ZMod 981270131) ^ 490635065 = ((981270130 : ℕ) : ZMod 981270131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (981270131 - 1) / 5 = 196254026 from by norm_num]
      have h2 : (2 : ZMod 981270131) ^ 196254026 = ((73980242 : ℕ) : ZMod 981270131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (981270131 - 1) / 607 = 1616590 from by norm_num]
      have h2 : (2 : ZMod 981270131) ^ 1616590 = ((358765927 : ℕ) : ZMod 981270131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (981270131 - 1) / 161659 = 6070 from by norm_num]
      have h2 : (2 : ZMod 981270131) ^ 6070 = ((485244219 : ℕ) : ZMod 981270131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1962540263 : Nat.Prime 1962540263 := by
  refine lucas_primality 1962540263 (5 : ZMod 1962540263) ?_ (fun q hq hd => ?_)
  · rw [show 1962540263 - 1 = 1962540262 from by norm_num]
    reduce_mod_char
  · have e : 1962540263 - 1 = [2 ^ 1, 981270131 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1962540263 - 1) / 2 = 981270131 from by norm_num]
      have h2 : (5 : ZMod 1962540263) ^ 981270131 = ((1962540262 : ℕ) : ZMod 1962540263) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_981270131).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1962540263 - 1) / 981270131 = 2 from by norm_num]
      have h2 : (5 : ZMod 1962540263) ^ 2 = ((25 : ℕ) : ZMod 1962540263) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9399272583196421 : Nat.Prime 9399272583196421 := by
  refine lucas_primality 9399272583196421 (2 : ZMod 9399272583196421) ?_ (fun q hq hd => ?_)
  · rw [show 9399272583196421 - 1 = 9399272583196420 from by norm_num]
    reduce_mod_char
  · have e : 9399272583196421 - 1 = [2 ^ 2, 5 ^ 1, 43 ^ 1, 5569 ^ 1, 1962540263 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9399272583196421 - 1) / 2 = 4699636291598210 from by norm_num]
      have h2 : (2 : ZMod 9399272583196421) ^ 4699636291598210 = ((9399272583196420 : ℕ) : ZMod 9399272583196421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9399272583196421 - 1) / 5 = 1879854516639284 from by norm_num]
      have h2 : (2 : ZMod 9399272583196421) ^ 1879854516639284 = ((4940137961036853 : ℕ) : ZMod 9399272583196421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9399272583196421 - 1) / 43 = 218587734492940 from by norm_num]
      have h2 : (2 : ZMod 9399272583196421) ^ 218587734492940 = ((9085087145793697 : ℕ) : ZMod 9399272583196421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9399272583196421 - 1) / 5569 = 1687784626180 from by norm_num]
      have h2 : (2 : ZMod 9399272583196421) ^ 1687784626180 = ((8092268430703922 : ℕ) : ZMod 9399272583196421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1962540263).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9399272583196421 - 1) / 1962540263 = 4789340 from by norm_num]
      have h2 : (2 : ZMod 9399272583196421) ^ 4789340 = ((5685192705244580 : ℕ) : ZMod 9399272583196421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_138626844763792224081439 : Nat.Prime 138626844763792224081439 := by
  refine lucas_primality 138626844763792224081439 (3 : ZMod 138626844763792224081439) ?_ (fun q hq hd => ?_)
  · rw [show 138626844763792224081439 - 1 = 138626844763792224081438 from by norm_num]
    reduce_mod_char
  · have e : 138626844763792224081439 - 1 = [2 ^ 1, 3 ^ 2, 7 ^ 1, 117053 ^ 1, 9399272583196421 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138626844763792224081439 - 1) / 2 = 69313422381896112040719 from by norm_num]
      have h2 : (3 : ZMod 138626844763792224081439) ^ 69313422381896112040719 = ((138626844763792224081438 : ℕ) : ZMod 138626844763792224081439) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138626844763792224081439 - 1) / 3 = 46208948254597408027146 from by norm_num]
      have h2 : (3 : ZMod 138626844763792224081439) ^ 46208948254597408027146 = ((85724203307334615865728 : ℕ) : ZMod 138626844763792224081439) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138626844763792224081439 - 1) / 7 = 19803834966256032011634 from by norm_num]
      have h2 : (3 : ZMod 138626844763792224081439) ^ 19803834966256032011634 = ((135052985565196690497694 : ℕ) : ZMod 138626844763792224081439) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138626844763792224081439 - 1) / 117053 = 1184308345482749046 from by norm_num]
      have h2 : (3 : ZMod 138626844763792224081439) ^ 1184308345482749046 = ((30820129770896974446072 : ℕ) : ZMod 138626844763792224081439) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_9399272583196421).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138626844763792224081439 - 1) / 9399272583196421 = 14748678 from by norm_num]
      have h2 : (3 : ZMod 138626844763792224081439) ^ 14748678 = ((130299981820635127312380 : ℕ) : ZMod 138626844763792224081439) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4900402101963269918180361130213343099 : Nat.Prime 4900402101963269918180361130213343099 := by
  refine lucas_primality 4900402101963269918180361130213343099 (6 : ZMod 4900402101963269918180361130213343099) ?_ (fun q hq hd => ?_)
  · rw [show 4900402101963269918180361130213343099 - 1 = 4900402101963269918180361130213343098 from by norm_num]
    reduce_mod_char
  · have e : 4900402101963269918180361130213343099 - 1 = [2 ^ 1, 7 ^ 1, 719 ^ 1, 3511781227 ^ 1, 138626844763792224081439 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4900402101963269918180361130213343099 - 1) / 2 = 2450201050981634959090180565106671549 from by norm_num]
      have h2 : (6 : ZMod 4900402101963269918180361130213343099) ^ 2450201050981634959090180565106671549 = ((4900402101963269918180361130213343098 : ℕ) : ZMod 4900402101963269918180361130213343099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4900402101963269918180361130213343099 - 1) / 7 = 700057443137609988311480161459049014 from by norm_num]
      have h2 : (6 : ZMod 4900402101963269918180361130213343099) ^ 700057443137609988311480161459049014 = ((3687343651878426297745623100611884205 : ℕ) : ZMod 4900402101963269918180361130213343099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4900402101963269918180361130213343099 - 1) / 719 = 6815580113996202946008847190839142 from by norm_num]
      have h2 : (6 : ZMod 4900402101963269918180361130213343099) ^ 6815580113996202946008847190839142 = ((3528212470737366580412810644362084226 : ℕ) : ZMod 4900402101963269918180361130213343099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3511781227).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4900402101963269918180361130213343099 - 1) / 3511781227 = 1395417819392332527603764974 from by norm_num]
      have h2 : (6 : ZMod 4900402101963269918180361130213343099) ^ 1395417819392332527603764974 = ((1353577574554682435522896987180958913 : ℕ) : ZMod 4900402101963269918180361130213343099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_138626844763792224081439).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4900402101963269918180361130213343099 - 1) / 138626844763792224081439 = 35349589830982 from by norm_num]
      have h2 : (6 : ZMod 4900402101963269918180361130213343099) ^ 35349589830982 = ((526289787085844511347310773414909648 : ℕ) : ZMod 4900402101963269918180361130213343099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_25491056464897 : Nat.Prime 25491056464897 := by
  refine lucas_primality 25491056464897 (5 : ZMod 25491056464897) ?_ (fun q hq hd => ?_)
  · rw [show 25491056464897 - 1 = 25491056464896 from by norm_num]
    reduce_mod_char
  · have e : 25491056464897 - 1 = [2 ^ 10, 3 ^ 1, 11 ^ 1, 19 ^ 1, 39702727 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25491056464897 - 1) / 2 = 12745528232448 from by norm_num]
      have h2 : (5 : ZMod 25491056464897) ^ 12745528232448 = ((25491056464896 : ℕ) : ZMod 25491056464897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25491056464897 - 1) / 3 = 8497018821632 from by norm_num]
      have h2 : (5 : ZMod 25491056464897) ^ 8497018821632 = ((17672048799729 : ℕ) : ZMod 25491056464897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25491056464897 - 1) / 11 = 2317368769536 from by norm_num]
      have h2 : (5 : ZMod 25491056464897) ^ 2317368769536 = ((10704982305913 : ℕ) : ZMod 25491056464897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25491056464897 - 1) / 19 = 1341634550784 from by norm_num]
      have h2 : (5 : ZMod 25491056464897) ^ 1341634550784 = ((4539264078483 : ℕ) : ZMod 25491056464897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25491056464897 - 1) / 39702727 = 642048 from by norm_num]
      have h2 : (5 : ZMod 25491056464897) ^ 642048 = ((8445340234953 : ℕ) : ZMod 25491056464897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_175187263 : Nat.Prime 175187263 := by
  refine lucas_primality 175187263 (5 : ZMod 175187263) ?_ (fun q hq hd => ?_)
  · rw [show 175187263 - 1 = 175187262 from by norm_num]
    reduce_mod_char
  · have e : 175187263 - 1 = [2 ^ 1, 3 ^ 1, 31 ^ 1, 199 ^ 1, 4733 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175187263 - 1) / 2 = 87593631 from by norm_num]
      have h2 : (5 : ZMod 175187263) ^ 87593631 = ((175187262 : ℕ) : ZMod 175187263) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175187263 - 1) / 3 = 58395754 from by norm_num]
      have h2 : (5 : ZMod 175187263) ^ 58395754 = ((173587916 : ℕ) : ZMod 175187263) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175187263 - 1) / 31 = 5651202 from by norm_num]
      have h2 : (5 : ZMod 175187263) ^ 5651202 = ((66722766 : ℕ) : ZMod 175187263) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175187263 - 1) / 199 = 880338 from by norm_num]
      have h2 : (5 : ZMod 175187263) ^ 880338 = ((34450738 : ℕ) : ZMod 175187263) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175187263 - 1) / 4733 = 37014 from by norm_num]
      have h2 : (5 : ZMod 175187263) ^ 37014 = ((33355183 : ℕ) : ZMod 175187263) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3867806687195463907 : Nat.Prime 3867806687195463907 := by
  refine lucas_primality 3867806687195463907 (2 : ZMod 3867806687195463907) ?_ (fun q hq hd => ?_)
  · rw [show 3867806687195463907 - 1 = 3867806687195463906 from by norm_num]
    reduce_mod_char
  · have e : 3867806687195463907 - 1 = [2 ^ 1, 3 ^ 1, 19 ^ 1, 571 ^ 1, 339173 ^ 1, 175187263 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3867806687195463907 - 1) / 2 = 1933903343597731953 from by norm_num]
      have h2 : (2 : ZMod 3867806687195463907) ^ 1933903343597731953 = ((3867806687195463906 : ℕ) : ZMod 3867806687195463907) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3867806687195463907 - 1) / 3 = 1289268895731821302 from by norm_num]
      have h2 : (2 : ZMod 3867806687195463907) ^ 1289268895731821302 = ((2842436699122913648 : ℕ) : ZMod 3867806687195463907) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3867806687195463907 - 1) / 19 = 203568773010287574 from by norm_num]
      have h2 : (2 : ZMod 3867806687195463907) ^ 203568773010287574 = ((461475748599923503 : ℕ) : ZMod 3867806687195463907) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3867806687195463907 - 1) / 571 = 6773742009098886 from by norm_num]
      have h2 : (2 : ZMod 3867806687195463907) ^ 6773742009098886 = ((3323987631845560247 : ℕ) : ZMod 3867806687195463907) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3867806687195463907 - 1) / 339173 = 11403639697722 from by norm_num]
      have h2 : (2 : ZMod 3867806687195463907) ^ 11403639697722 = ((2042993852905446868 : ℕ) : ZMod 3867806687195463907) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_175187263).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3867806687195463907 - 1) / 175187263 = 22078127262 from by norm_num]
      have h2 : (2 : ZMod 3867806687195463907) ^ 22078127262 = ((1170401107696164839 : ℕ) : ZMod 3867806687195463907) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6310046634150769846811224062245057 : Nat.Prime 6310046634150769846811224062245057 := by
  refine lucas_primality 6310046634150769846811224062245057 (3 : ZMod 6310046634150769846811224062245057) ?_ (fun q hq hd => ?_)
  · rw [show 6310046634150769846811224062245057 - 1 = 6310046634150769846811224062245056 from by norm_num]
    reduce_mod_char
  · have e : 6310046634150769846811224062245057 - 1 = [2 ^ 6, 25491056464897 ^ 1, 3867806687195463907 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6310046634150769846811224062245057 - 1) / 2 = 3155023317075384923405612031122528 from by norm_num]
      have h2 : (3 : ZMod 6310046634150769846811224062245057) ^ 3155023317075384923405612031122528 = ((6310046634150769846811224062245056 : ℕ) : ZMod 6310046634150769846811224062245057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_25491056464897).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6310046634150769846811224062245057 - 1) / 25491056464897 = 247539627980509690048 from by norm_num]
      have h2 : (3 : ZMod 6310046634150769846811224062245057) ^ 247539627980509690048 = ((5893058894620226287541339888691500 : ℕ) : ZMod 6310046634150769846811224062245057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3867806687195463907).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6310046634150769846811224062245057 - 1) / 3867806687195463907 = 1631427613753408 from by norm_num]
      have h2 : (3 : ZMod 6310046634150769846811224062245057) ^ 1631427613753408 = ((1058125228490907049068691785814524 : ℕ) : ZMod 6310046634150769846811224062245057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_294422295816364674005620478775270165629531 : Nat.Prime 294422295816364674005620478775270165629531 := by
  refine lucas_primality 294422295816364674005620478775270165629531 (2 : ZMod 294422295816364674005620478775270165629531) ?_ (fun q hq hd => ?_)
  · rw [show 294422295816364674005620478775270165629531 - 1 = 294422295816364674005620478775270165629530 from by norm_num]
    reduce_mod_char
  · have e : 294422295816364674005620478775270165629531 - 1 = [2 ^ 1, 5 ^ 1, 709 ^ 1, 6581 ^ 1, 6310046634150769846811224062245057 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (294422295816364674005620478775270165629531 - 1) / 2 = 147211147908182337002810239387635082814765 from by norm_num]
      have h2 : (2 : ZMod 294422295816364674005620478775270165629531) ^ 147211147908182337002810239387635082814765 = ((294422295816364674005620478775270165629530 : ℕ) : ZMod 294422295816364674005620478775270165629531) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (294422295816364674005620478775270165629531 - 1) / 5 = 58884459163272934801124095755054033125906 from by norm_num]
      have h2 : (2 : ZMod 294422295816364674005620478775270165629531) ^ 58884459163272934801124095755054033125906 = ((190106803170030597740086217544097705114242 : ℕ) : ZMod 294422295816364674005620478775270165629531) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (294422295816364674005620478775270165629531 - 1) / 709 = 415264168993462163618646655536347201170 from by norm_num]
      have h2 : (2 : ZMod 294422295816364674005620478775270165629531) ^ 415264168993462163618646655536347201170 = ((216162624203562245862913574106222333376505 : ℕ) : ZMod 294422295816364674005620478775270165629531) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (294422295816364674005620478775270165629531 - 1) / 6581 = 44738230636128958213891578601317454130 from by norm_num]
      have h2 : (2 : ZMod 294422295816364674005620478775270165629531) ^ 44738230636128958213891578601317454130 = ((184669756045095964674026459938541730186317 : ℕ) : ZMod 294422295816364674005620478775270165629531) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6310046634150769846811224062245057).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (294422295816364674005620478775270165629531 - 1) / 6310046634150769846811224062245057 = 46659290 from by norm_num]
      have h2 : (2 : ZMod 294422295816364674005620478775270165629531) ^ 46659290 = ((164153223847197082143728603460955127387115 : ℕ) : ZMod 294422295816364674005620478775270165629531) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15044222650915986784475012020785853019343366205331 : Nat.Prime 15044222650915986784475012020785853019343366205331 := by
  refine lucas_primality 15044222650915986784475012020785853019343366205331 (10 : ZMod 15044222650915986784475012020785853019343366205331) ?_ (fun q hq hd => ?_)
  · rw [show 15044222650915986784475012020785853019343366205331 - 1 = 15044222650915986784475012020785853019343366205330 from by norm_num]
    reduce_mod_char
  · have e : 15044222650915986784475012020785853019343366205331 - 1 = [2 ^ 1, 5 ^ 1, 733 ^ 1, 6971 ^ 1, 294422295816364674005620478775270165629531 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15044222650915986784475012020785853019343366205331 - 1) / 2 = 7522111325457993392237506010392926509671683102665 from by norm_num]
      have h2 : (10 : ZMod 15044222650915986784475012020785853019343366205331) ^ 7522111325457993392237506010392926509671683102665 = ((15044222650915986784475012020785853019343366205330 : ℕ) : ZMod 15044222650915986784475012020785853019343366205331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15044222650915986784475012020785853019343366205331 - 1) / 5 = 3008844530183197356895002404157170603868673241066 from by norm_num]
      have h2 : (10 : ZMod 15044222650915986784475012020785853019343366205331) ^ 3008844530183197356895002404157170603868673241066 = ((6828434825719431803908311317324120890925452347409 : ℕ) : ZMod 15044222650915986784475012020785853019343366205331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15044222650915986784475012020785853019343366205331 - 1) / 733 = 20524178241358781424931803575424083246034606010 from by norm_num]
      have h2 : (10 : ZMod 15044222650915986784475012020785853019343366205331) ^ 20524178241358781424931803575424083246034606010 = ((10712891636271999951014348387909273592453561084171 : ℕ) : ZMod 15044222650915986784475012020785853019343366205331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15044222650915986784475012020785853019343366205331 - 1) / 6971 = 2158115428333953060461198109422730314064462230 from by norm_num]
      have h2 : (10 : ZMod 15044222650915986784475012020785853019343366205331) ^ 2158115428333953060461198109422730314064462230 = ((14244069804642153591142282977075423468848050782573 : ℕ) : ZMod 15044222650915986784475012020785853019343366205331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_294422295816364674005620478775270165629531).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15044222650915986784475012020785853019343366205331 - 1) / 294422295816364674005620478775270165629531 = 51097430 from by norm_num]
      have h2 : (10 : ZMod 15044222650915986784475012020785853019343366205331) ^ 51097430 = ((8628775635217520294949119020065804136076337538734 : ℕ) : ZMod 15044222650915986784475012020785853019343366205331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_417817067 : Nat.Prime 417817067 := by
  refine lucas_primality 417817067 (5 : ZMod 417817067) ?_ (fun q hq hd => ?_)
  · rw [show 417817067 - 1 = 417817066 from by norm_num]
    reduce_mod_char
  · have e : 417817067 - 1 = [2 ^ 1, 757 ^ 1, 275969 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (417817067 - 1) / 2 = 208908533 from by norm_num]
      have h2 : (5 : ZMod 417817067) ^ 208908533 = ((417817066 : ℕ) : ZMod 417817067) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (417817067 - 1) / 757 = 551938 from by norm_num]
      have h2 : (5 : ZMod 417817067) ^ 551938 = ((95132019 : ℕ) : ZMod 417817067) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (417817067 - 1) / 275969 = 1514 from by norm_num]
      have h2 : (5 : ZMod 417817067) ^ 1514 = ((402992213 : ℕ) : ZMod 417817067) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1485778288798957523 : Nat.Prime 1485778288798957523 := by
  refine lucas_primality 1485778288798957523 (5 : ZMod 1485778288798957523) ?_ (fun q hq hd => ?_)
  · rw [show 1485778288798957523 - 1 = 1485778288798957522 from by norm_num]
    reduce_mod_char
  · have e : 1485778288798957523 - 1 = [2 ^ 1, 761 ^ 1, 55051 ^ 1, 92831 ^ 1, 191021 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1485778288798957523 - 1) / 2 = 742889144399478761 from by norm_num]
      have h2 : (5 : ZMod 1485778288798957523) ^ 742889144399478761 = ((1485778288798957522 : ℕ) : ZMod 1485778288798957523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1485778288798957523 - 1) / 761 = 1952402481996002 from by norm_num]
      have h2 : (5 : ZMod 1485778288798957523) ^ 1952402481996002 = ((16777216 : ℕ) : ZMod 1485778288798957523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1485778288798957523 - 1) / 55051 = 26989124426422 from by norm_num]
      have h2 : (5 : ZMod 1485778288798957523) ^ 26989124426422 = ((788652597345617868 : ℕ) : ZMod 1485778288798957523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1485778288798957523 - 1) / 92831 = 16005195342062 from by norm_num]
      have h2 : (5 : ZMod 1485778288798957523) ^ 16005195342062 = ((253063976348999588 : ℕ) : ZMod 1485778288798957523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1485778288798957523 - 1) / 191021 = 7778088737882 from by norm_num]
      have h2 : (5 : ZMod 1485778288798957523) ^ 7778088737882 = ((1320659687966717068 : ℕ) : ZMod 1485778288798957523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_86369467 : Nat.Prime 86369467 := by
  refine lucas_primality 86369467 (5 : ZMod 86369467) ?_ (fun q hq hd => ?_)
  · rw [show 86369467 - 1 = 86369466 from by norm_num]
    reduce_mod_char
  · have e : 86369467 - 1 = [2 ^ 1, 3 ^ 1, 769 ^ 1, 18719 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86369467 - 1) / 2 = 43184733 from by norm_num]
      have h2 : (5 : ZMod 86369467) ^ 43184733 = ((86369466 : ℕ) : ZMod 86369467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86369467 - 1) / 3 = 28789822 from by norm_num]
      have h2 : (5 : ZMod 86369467) ^ 28789822 = ((82389833 : ℕ) : ZMod 86369467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86369467 - 1) / 769 = 112314 from by norm_num]
      have h2 : (5 : ZMod 86369467) ^ 112314 = ((53674911 : ℕ) : ZMod 86369467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86369467 - 1) / 18719 = 4614 from by norm_num]
      have h2 : (5 : ZMod 86369467) ^ 4614 = ((36265782 : ℕ) : ZMod 86369467) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3128212463 : Nat.Prime 3128212463 := by
  refine lucas_primality 3128212463 (5 : ZMod 3128212463) ?_ (fun q hq hd => ?_)
  · rw [show 3128212463 - 1 = 3128212462 from by norm_num]
    reduce_mod_char
  · have e : 3128212463 - 1 = [2 ^ 1, 29303 ^ 1, 53377 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3128212463 - 1) / 2 = 1564106231 from by norm_num]
      have h2 : (5 : ZMod 3128212463) ^ 1564106231 = ((3128212462 : ℕ) : ZMod 3128212463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3128212463 - 1) / 29303 = 106754 from by norm_num]
      have h2 : (5 : ZMod 3128212463) ^ 106754 = ((3068344610 : ℕ) : ZMod 3128212463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3128212463 - 1) / 53377 = 58606 from by norm_num]
      have h2 : (5 : ZMod 3128212463) ^ 58606 = ((2013205783 : ℕ) : ZMod 3128212463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_858540241581349863214463 : Nat.Prime 858540241581349863214463 := by
  refine lucas_primality 858540241581349863214463 (5 : ZMod 858540241581349863214463) ?_ (fun q hq hd => ?_)
  · rw [show 858540241581349863214463 - 1 = 858540241581349863214462 from by norm_num]
    reduce_mod_char
  · have e : 858540241581349863214463 - 1 = [2 ^ 1, 7 ^ 1, 631 ^ 1, 6343 ^ 1, 4897927 ^ 1, 3128212463 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (858540241581349863214463 - 1) / 2 = 429270120790674931607231 from by norm_num]
      have h2 : (5 : ZMod 858540241581349863214463) ^ 429270120790674931607231 = ((858540241581349863214462 : ℕ) : ZMod 858540241581349863214463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (858540241581349863214463 - 1) / 7 = 122648605940192837602066 from by norm_num]
      have h2 : (5 : ZMod 858540241581349863214463) ^ 122648605940192837602066 = ((847002819889914643742717 : ℕ) : ZMod 858540241581349863214463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (858540241581349863214463 - 1) / 631 = 1360602601555229577202 from by norm_num]
      have h2 : (5 : ZMod 858540241581349863214463) ^ 1360602601555229577202 = ((401691220002161519475733 : ℕ) : ZMod 858540241581349863214463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (858540241581349863214463 - 1) / 6343 = 135352395015189951634 from by norm_num]
      have h2 : (5 : ZMod 858540241581349863214463) ^ 135352395015189951634 = ((791728909266324634826525 : ℕ) : ZMod 858540241581349863214463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (858540241581349863214463 - 1) / 4897927 = 175286451100914706 from by norm_num]
      have h2 : (5 : ZMod 858540241581349863214463) ^ 175286451100914706 = ((17631443251432478053368 : ℕ) : ZMod 858540241581349863214463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3128212463).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (858540241581349863214463 - 1) / 3128212463 = 274450745189474 from by norm_num]
      have h2 : (5 : ZMod 858540241581349863214463) ^ 274450745189474 = ((710917587820548522461253 : ℕ) : ZMod 858540241581349863214463) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5405369360996178738798259049 : Nat.Prime 5405369360996178738798259049 := by
  refine lucas_primality 5405369360996178738798259049 (3 : ZMod 5405369360996178738798259049) ?_ (fun q hq hd => ?_)
  · rw [show 5405369360996178738798259049 - 1 = 5405369360996178738798259048 from by norm_num]
    reduce_mod_char
  · have e : 5405369360996178738798259049 - 1 = [2 ^ 3, 787 ^ 1, 858540241581349863214463 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5405369360996178738798259049 - 1) / 2 = 2702684680498089369399129524 from by norm_num]
      have h2 : (3 : ZMod 5405369360996178738798259049) ^ 2702684680498089369399129524 = ((5405369360996178738798259048 : ℕ) : ZMod 5405369360996178738798259049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5405369360996178738798259049 - 1) / 787 = 6868321932650798905715704 from by norm_num]
      have h2 : (3 : ZMod 5405369360996178738798259049) ^ 6868321932650798905715704 = ((668712536352967118172373846 : ℕ) : ZMod 5405369360996178738798259049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_858540241581349863214463).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5405369360996178738798259049 - 1) / 858540241581349863214463 = 6296 from by norm_num]
      have h2 : (3 : ZMod 5405369360996178738798259049) ^ 6296 = ((2200483217175096436732156460 : ℕ) : ZMod 5405369360996178738798259049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_101034925780539468379 : Nat.Prime 101034925780539468379 := by
  refine lucas_primality 101034925780539468379 (2 : ZMod 101034925780539468379) ?_ (fun q hq hd => ?_)
  · rw [show 101034925780539468379 - 1 = 101034925780539468378 from by norm_num]
    reduce_mod_char
  · have e : 101034925780539468379 - 1 = [2 ^ 1, 3 ^ 1, 430013 ^ 1, 5175719 ^ 1, 7566029 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (101034925780539468379 - 1) / 2 = 50517462890269734189 from by norm_num]
      have h2 : (2 : ZMod 101034925780539468379) ^ 50517462890269734189 = ((101034925780539468378 : ℕ) : ZMod 101034925780539468379) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (101034925780539468379 - 1) / 3 = 33678308593513156126 from by norm_num]
      have h2 : (2 : ZMod 101034925780539468379) ^ 33678308593513156126 = ((35982606297532442216 : ℕ) : ZMod 101034925780539468379) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (101034925780539468379 - 1) / 430013 = 234957840299106 from by norm_num]
      have h2 : (2 : ZMod 101034925780539468379) ^ 234957840299106 = ((67905456864803112272 : ℕ) : ZMod 101034925780539468379) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (101034925780539468379 - 1) / 5175719 = 19520944970262 from by norm_num]
      have h2 : (2 : ZMod 101034925780539468379) ^ 19520944970262 = ((36379121031952602414 : ℕ) : ZMod 101034925780539468379) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (101034925780539468379 - 1) / 7566029 = 13353758726082 from by norm_num]
      have h2 : (2 : ZMod 101034925780539468379) ^ 13353758726082 = ((37144490420745179568 : ℕ) : ZMod 101034925780539468379) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1037866321911576169081957409 : Nat.Prime 1037866321911576169081957409 := by
  refine lucas_primality 1037866321911576169081957409 (3 : ZMod 1037866321911576169081957409) ?_ (fun q hq hd => ?_)
  · rw [show 1037866321911576169081957409 - 1 = 1037866321911576169081957408 from by norm_num]
    reduce_mod_char
  · have e : 1037866321911576169081957409 - 1 = [2 ^ 5, 17 ^ 1, 23 ^ 1, 821 ^ 1, 101034925780539468379 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1037866321911576169081957409 - 1) / 2 = 518933160955788084540978704 from by norm_num]
      have h2 : (3 : ZMod 1037866321911576169081957409) ^ 518933160955788084540978704 = ((1037866321911576169081957408 : ℕ) : ZMod 1037866321911576169081957409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1037866321911576169081957409 - 1) / 17 = 61050960112445657004821024 from by norm_num]
      have h2 : (3 : ZMod 1037866321911576169081957409) ^ 61050960112445657004821024 = ((927967340095705840145224914 : ℕ) : ZMod 1037866321911576169081957409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1037866321911576169081957409 - 1) / 23 = 45124622691807659525302496 from by norm_num]
      have h2 : (3 : ZMod 1037866321911576169081957409) ^ 45124622691807659525302496 = ((30342866053799126381283295 : ℕ) : ZMod 1037866321911576169081957409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1037866321911576169081957409 - 1) / 821 = 1264148991366109828358048 from by norm_num]
      have h2 : (3 : ZMod 1037866321911576169081957409) ^ 1264148991366109828358048 = ((913304294695911854349696501 : ℕ) : ZMod 1037866321911576169081957409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_101034925780539468379).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1037866321911576169081957409 - 1) / 101034925780539468379 = 10272352 from by norm_num]
      have h2 : (3 : ZMod 1037866321911576169081957409) ^ 10272352 = ((476807543471173932279142053 : ℕ) : ZMod 1037866321911576169081957409) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_13615553872073 : Nat.Prime 13615553872073 := by
  refine lucas_primality 13615553872073 (3 : ZMod 13615553872073) ?_ (fun q hq hd => ?_)
  · rw [show 13615553872073 - 1 = 13615553872072 from by norm_num]
    reduce_mod_char
  · have e : 13615553872073 - 1 = [2 ^ 3, 47 ^ 1, 823 ^ 1, 3719 ^ 1, 11831 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13615553872073 - 1) / 2 = 6807776936036 from by norm_num]
      have h2 : (3 : ZMod 13615553872073) ^ 6807776936036 = ((13615553872072 : ℕ) : ZMod 13615553872073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13615553872073 - 1) / 47 = 289692635576 from by norm_num]
      have h2 : (3 : ZMod 13615553872073) ^ 289692635576 = ((10796968199687 : ℕ) : ZMod 13615553872073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13615553872073 - 1) / 823 = 16543807864 from by norm_num]
      have h2 : (3 : ZMod 13615553872073) ^ 16543807864 = ((8450409927006 : ℕ) : ZMod 13615553872073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13615553872073 - 1) / 3719 = 3661079288 from by norm_num]
      have h2 : (3 : ZMod 13615553872073) ^ 3661079288 = ((9367358803652 : ℕ) : ZMod 13615553872073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13615553872073 - 1) / 11831 = 1150837112 from by norm_num]
      have h2 : (3 : ZMod 13615553872073) ^ 1150837112 = ((4520674836059 : ℕ) : ZMod 13615553872073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_131147801 : Nat.Prime 131147801 := by
  refine lucas_primality 131147801 (3 : ZMod 131147801) ?_ (fun q hq hd => ?_)
  · rw [show 131147801 - 1 = 131147800 from by norm_num]
    reduce_mod_char
  · have e : 131147801 - 1 = [2 ^ 3, 5 ^ 2, 7 ^ 1, 113 ^ 1, 829 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131147801 - 1) / 2 = 65573900 from by norm_num]
      have h2 : (3 : ZMod 131147801) ^ 65573900 = ((131147800 : ℕ) : ZMod 131147801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131147801 - 1) / 5 = 26229560 from by norm_num]
      have h2 : (3 : ZMod 131147801) ^ 26229560 = ((17282445 : ℕ) : ZMod 131147801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131147801 - 1) / 7 = 18735400 from by norm_num]
      have h2 : (3 : ZMod 131147801) ^ 18735400 = ((118307075 : ℕ) : ZMod 131147801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131147801 - 1) / 113 = 1160600 from by norm_num]
      have h2 : (3 : ZMod 131147801) ^ 1160600 = ((16405508 : ℕ) : ZMod 131147801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131147801 - 1) / 829 = 158200 from by norm_num]
      have h2 : (3 : ZMod 131147801) ^ 158200 = ((128780962 : ℕ) : ZMod 131147801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3475782313453 : Nat.Prime 3475782313453 := by
  refine lucas_primality 3475782313453 (2 : ZMod 3475782313453) ?_ (fun q hq hd => ?_)
  · rw [show 3475782313453 - 1 = 3475782313452 from by norm_num]
    reduce_mod_char
  · have e : 3475782313453 - 1 = [2 ^ 2, 3 ^ 3, 63737 ^ 1, 504937 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3475782313453 - 1) / 2 = 1737891156726 from by norm_num]
      have h2 : (2 : ZMod 3475782313453) ^ 1737891156726 = ((3475782313452 : ℕ) : ZMod 3475782313453) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3475782313453 - 1) / 3 = 1158594104484 from by norm_num]
      have h2 : (2 : ZMod 3475782313453) ^ 1158594104484 = ((93396722602 : ℕ) : ZMod 3475782313453) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3475782313453 - 1) / 63737 = 54533196 from by norm_num]
      have h2 : (2 : ZMod 3475782313453) ^ 54533196 = ((987414145102 : ℕ) : ZMod 3475782313453) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3475782313453 - 1) / 504937 = 6883596 from by norm_num]
      have h2 : (2 : ZMod 3475782313453) ^ 6883596 = ((1086217114372 : ℕ) : ZMod 3475782313453) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_290909945452340651251 : Nat.Prime 290909945452340651251 := by
  refine lucas_primality 290909945452340651251 (3 : ZMod 290909945452340651251) ?_ (fun q hq hd => ?_)
  · rw [show 290909945452340651251 - 1 = 290909945452340651250 from by norm_num]
    reduce_mod_char
  · have e : 290909945452340651251 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 4, 11 ^ 1, 2029 ^ 1, 3475782313453 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (290909945452340651251 - 1) / 2 = 145454972726170325625 from by norm_num]
      have h2 : (3 : ZMod 290909945452340651251) ^ 145454972726170325625 = ((290909945452340651250 : ℕ) : ZMod 290909945452340651251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (290909945452340651251 - 1) / 3 = 96969981817446883750 from by norm_num]
      have h2 : (3 : ZMod 290909945452340651251) ^ 96969981817446883750 = ((154144872806677296244 : ℕ) : ZMod 290909945452340651251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (290909945452340651251 - 1) / 5 = 58181989090468130250 from by norm_num]
      have h2 : (3 : ZMod 290909945452340651251) ^ 58181989090468130250 = ((127318667932037483102 : ℕ) : ZMod 290909945452340651251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (290909945452340651251 - 1) / 11 = 26446358677485513750 from by norm_num]
      have h2 : (3 : ZMod 290909945452340651251) ^ 26446358677485513750 = ((196160013638237086160 : ℕ) : ZMod 290909945452340651251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (290909945452340651251 - 1) / 2029 = 143376020429936250 from by norm_num]
      have h2 : (3 : ZMod 290909945452340651251) ^ 143376020429936250 = ((139157760722219097849 : ℕ) : ZMod 290909945452340651251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3475782313453).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (290909945452340651251 - 1) / 3475782313453 = 83696250 from by norm_num]
      have h2 : (3 : ZMod 290909945452340651251) ^ 83696250 = ((198599624194610956854 : ℕ) : ZMod 290909945452340651251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1377062372371126895706481139 : Nat.Prime 1377062372371126895706481139 := by
  refine lucas_primality 1377062372371126895706481139 (6 : ZMod 1377062372371126895706481139) ?_ (fun q hq hd => ?_)
  · rw [show 1377062372371126895706481139 - 1 = 1377062372371126895706481138 from by norm_num]
    reduce_mod_char
  · have e : 1377062372371126895706481139 - 1 = [2 ^ 1, 7 ^ 1, 13 ^ 1, 31 ^ 1, 839 ^ 1, 290909945452340651251 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1377062372371126895706481139 - 1) / 2 = 688531186185563447853240569 from by norm_num]
      have h2 : (6 : ZMod 1377062372371126895706481139) ^ 688531186185563447853240569 = ((1377062372371126895706481138 : ℕ) : ZMod 1377062372371126895706481139) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1377062372371126895706481139 - 1) / 7 = 196723196053018127958068734 from by norm_num]
      have h2 : (6 : ZMod 1377062372371126895706481139) ^ 196723196053018127958068734 = ((1009716733404420295756897525 : ℕ) : ZMod 1377062372371126895706481139) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1377062372371126895706481139 - 1) / 13 = 105927874797778991977421626 from by norm_num]
      have h2 : (6 : ZMod 1377062372371126895706481139) ^ 105927874797778991977421626 = ((1369088033038848311204700239 : ℕ) : ZMod 1377062372371126895706481139) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1377062372371126895706481139 - 1) / 31 = 44421366850681512764725198 from by norm_num]
      have h2 : (6 : ZMod 1377062372371126895706481139) ^ 44421366850681512764725198 = ((275207160849271463550015174 : ℕ) : ZMod 1377062372371126895706481139) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1377062372371126895706481139 - 1) / 839 = 1641313912242105954358142 from by norm_num]
      have h2 : (6 : ZMod 1377062372371126895706481139) ^ 1641313912242105954358142 = ((905375608653978258507572781 : ℕ) : ZMod 1377062372371126895706481139) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_290909945452340651251).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1377062372371126895706481139 - 1) / 290909945452340651251 = 4733638 from by norm_num]
      have h2 : (6 : ZMod 1377062372371126895706481139) ^ 4733638 = ((1046154389605592870121241039 : ℕ) : ZMod 1377062372371126895706481139) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_30140194213 : Nat.Prime 30140194213 := by
  refine lucas_primality 30140194213 (2 : ZMod 30140194213) ?_ (fun q hq hd => ?_)
  · rw [show 30140194213 - 1 = 30140194212 from by norm_num]
    reduce_mod_char
  · have e : 30140194213 - 1 = [2 ^ 2, 3 ^ 2, 349 ^ 1, 757 ^ 1, 3169 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30140194213 - 1) / 2 = 15070097106 from by norm_num]
      have h2 : (2 : ZMod 30140194213) ^ 15070097106 = ((30140194212 : ℕ) : ZMod 30140194213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30140194213 - 1) / 3 = 10046731404 from by norm_num]
      have h2 : (2 : ZMod 30140194213) ^ 10046731404 = ((29950455910 : ℕ) : ZMod 30140194213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30140194213 - 1) / 349 = 86361588 from by norm_num]
      have h2 : (2 : ZMod 30140194213) ^ 86361588 = ((7317276662 : ℕ) : ZMod 30140194213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30140194213 - 1) / 757 = 39815316 from by norm_num]
      have h2 : (2 : ZMod 30140194213) ^ 39815316 = ((11028311079 : ℕ) : ZMod 30140194213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30140194213 - 1) / 3169 = 9510948 from by norm_num]
      have h2 : (2 : ZMod 30140194213) ^ 9510948 = ((16075124282 : ℕ) : ZMod 30140194213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_48037657 : Nat.Prime 48037657 := by
  refine lucas_primality 48037657 (5 : ZMod 48037657) ?_ (fun q hq hd => ?_)
  · rw [show 48037657 - 1 = 48037656 from by norm_num]
    reduce_mod_char
  · have e : 48037657 - 1 = [2 ^ 3, 3 ^ 1, 113 ^ 1, 17713 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48037657 - 1) / 2 = 24018828 from by norm_num]
      have h2 : (5 : ZMod 48037657) ^ 24018828 = ((48037656 : ℕ) : ZMod 48037657) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48037657 - 1) / 3 = 16012552 from by norm_num]
      have h2 : (5 : ZMod 48037657) ^ 16012552 = ((44145829 : ℕ) : ZMod 48037657) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48037657 - 1) / 113 = 425112 from by norm_num]
      have h2 : (5 : ZMod 48037657) ^ 425112 = ((12377605 : ℕ) : ZMod 48037657) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48037657 - 1) / 17713 = 2712 from by norm_num]
      have h2 : (5 : ZMod 48037657) ^ 2712 = ((21917305 : ℕ) : ZMod 48037657) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_29768460950472271 : Nat.Prime 29768460950472271 := by
  refine lucas_primality 29768460950472271 (12 : ZMod 29768460950472271) ?_ (fun q hq hd => ?_)
  · rw [show 29768460950472271 - 1 = 29768460950472270 from by norm_num]
    reduce_mod_char
  · have e : 29768460950472271 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 13 ^ 1, 1588949 ^ 1, 48037657 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29768460950472271 - 1) / 2 = 14884230475236135 from by norm_num]
      have h2 : (12 : ZMod 29768460950472271) ^ 14884230475236135 = ((29768460950472270 : ℕ) : ZMod 29768460950472271) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29768460950472271 - 1) / 3 = 9922820316824090 from by norm_num]
      have h2 : (12 : ZMod 29768460950472271) ^ 9922820316824090 = ((27348379760608953 : ℕ) : ZMod 29768460950472271) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29768460950472271 - 1) / 5 = 5953692190094454 from by norm_num]
      have h2 : (12 : ZMod 29768460950472271) ^ 5953692190094454 = ((23871258262311164 : ℕ) : ZMod 29768460950472271) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29768460950472271 - 1) / 13 = 2289881611574790 from by norm_num]
      have h2 : (12 : ZMod 29768460950472271) ^ 2289881611574790 = ((10713952911761991 : ℕ) : ZMod 29768460950472271) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29768460950472271 - 1) / 1588949 = 18734686230 from by norm_num]
      have h2 : (12 : ZMod 29768460950472271) ^ 18734686230 = ((28199426422805962 : ℕ) : ZMod 29768460950472271) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_48037657).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29768460950472271 - 1) / 48037657 = 619690110 from by norm_num]
      have h2 : (12 : ZMod 29768460950472271) ^ 619690110 = ((5733198899591174 : ℕ) : ZMod 29768460950472271) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_252182368360125289180898199073630970779 : Nat.Prime 252182368360125289180898199073630970779 := by
  refine lucas_primality 252182368360125289180898199073630970779 (10 : ZMod 252182368360125289180898199073630970779) ?_ (fun q hq hd => ?_)
  · rw [show 252182368360125289180898199073630970779 - 1 = 252182368360125289180898199073630970778 from by norm_num]
    reduce_mod_char
  · have e : 252182368360125289180898199073630970779 - 1 = [2 ^ 1, 3 ^ 1, 139 ^ 1, 857 ^ 1, 393247 ^ 1, 30140194213 ^ 1, 29768460950472271 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (252182368360125289180898199073630970779 - 1) / 2 = 126091184180062644590449099536815485389 from by norm_num]
      have h2 : (10 : ZMod 252182368360125289180898199073630970779) ^ 126091184180062644590449099536815485389 = ((252182368360125289180898199073630970778 : ℕ) : ZMod 252182368360125289180898199073630970779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (252182368360125289180898199073630970779 - 1) / 3 = 84060789453375096393632733024543656926 from by norm_num]
      have h2 : (10 : ZMod 252182368360125289180898199073630970779) ^ 84060789453375096393632733024543656926 = ((187072444007047657383833795673649550858 : ℕ) : ZMod 252182368360125289180898199073630970779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (252182368360125289180898199073630970779 - 1) / 139 = 1814261642878599202740274813479359502 from by norm_num]
      have h2 : (10 : ZMod 252182368360125289180898199073630970779) ^ 1814261642878599202740274813479359502 = ((38009505945799523373512521925823595532 : ℕ) : ZMod 252182368360125289180898199073630970779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (252182368360125289180898199073630970779 - 1) / 857 = 294261806721266381774677011754528554 from by norm_num]
      have h2 : (10 : ZMod 252182368360125289180898199073630970779) ^ 294261806721266381774677011754528554 = ((60321921606579293531493472769743371730 : ℕ) : ZMod 252182368360125289180898199073630970779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (252182368360125289180898199073630970779 - 1) / 393247 = 641282370520627720442617996001574 from by norm_num]
      have h2 : (10 : ZMod 252182368360125289180898199073630970779) ^ 641282370520627720442617996001574 = ((35174934234155893700437799583085181441 : ℕ) : ZMod 252182368360125289180898199073630970779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_30140194213).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (252182368360125289180898199073630970779 - 1) / 30140194213 = 8366978878037705668346623506 from by norm_num]
      have h2 : (10 : ZMod 252182368360125289180898199073630970779) ^ 8366978878037705668346623506 = ((28677951651779920620730922271973667386 : ℕ) : ZMod 252182368360125289180898199073630970779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_29768460950472271).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (252182368360125289180898199073630970779 - 1) / 29768460950472271 = 8471461416151057806918 from by norm_num]
      have h2 : (10 : ZMod 252182368360125289180898199073630970779) ^ 8471461416151057806918 = ((81488293972640121821616894943814792322 : ℕ) : ZMod 252182368360125289180898199073630970779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_267946153 : Nat.Prime 267946153 := by
  refine lucas_primality 267946153 (7 : ZMod 267946153) ?_ (fun q hq hd => ?_)
  · rw [show 267946153 - 1 = 267946152 from by norm_num]
    reduce_mod_char
  · have e : 267946153 - 1 = [2 ^ 3, 3 ^ 1, 41 ^ 1, 317 ^ 1, 859 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267946153 - 1) / 2 = 133973076 from by norm_num]
      have h2 : (7 : ZMod 267946153) ^ 133973076 = ((267946152 : ℕ) : ZMod 267946153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267946153 - 1) / 3 = 89315384 from by norm_num]
      have h2 : (7 : ZMod 267946153) ^ 89315384 = ((48837336 : ℕ) : ZMod 267946153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267946153 - 1) / 41 = 6535272 from by norm_num]
      have h2 : (7 : ZMod 267946153) ^ 6535272 = ((132233685 : ℕ) : ZMod 267946153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267946153 - 1) / 317 = 845256 from by norm_num]
      have h2 : (7 : ZMod 267946153) ^ 845256 = ((53229908 : ℕ) : ZMod 267946153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267946153 - 1) / 859 = 311928 from by norm_num]
      have h2 : (7 : ZMod 267946153) ^ 311928 = ((157365200 : ℕ) : ZMod 267946153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_63384337 : Nat.Prime 63384337 := by
  refine lucas_primality 63384337 (17 : ZMod 63384337) ?_ (fun q hq hd => ?_)
  · rw [show 63384337 - 1 = 63384336 from by norm_num]
    reduce_mod_char
  · have e : 63384337 - 1 = [2 ^ 4, 3 ^ 3, 31 ^ 1, 4733 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63384337 - 1) / 2 = 31692168 from by norm_num]
      have h2 : (17 : ZMod 63384337) ^ 31692168 = ((63384336 : ℕ) : ZMod 63384337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63384337 - 1) / 3 = 21128112 from by norm_num]
      have h2 : (17 : ZMod 63384337) ^ 21128112 = ((19944861 : ℕ) : ZMod 63384337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63384337 - 1) / 31 = 2044656 from by norm_num]
      have h2 : (17 : ZMod 63384337) ^ 2044656 = ((11255684 : ℕ) : ZMod 63384337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63384337 - 1) / 4733 = 13392 from by norm_num]
      have h2 : (17 : ZMod 63384337) ^ 13392 = ((7424433 : ℕ) : ZMod 63384337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8156908781432775187914049 : Nat.Prime 8156908781432775187914049 := by
  refine lucas_primality 8156908781432775187914049 (23 : ZMod 8156908781432775187914049) ?_ (fun q hq hd => ?_)
  · rw [show 8156908781432775187914049 - 1 = 8156908781432775187914048 from by norm_num]
    reduce_mod_char
  · have e : 8156908781432775187914049 - 1 = [2 ^ 6, 3 ^ 1, 7 ^ 1, 907 ^ 1, 1279 ^ 1, 1553 ^ 1, 53149 ^ 1, 63384337 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8156908781432775187914049 - 1) / 2 = 4078454390716387593957024 from by norm_num]
      have h2 : (23 : ZMod 8156908781432775187914049) ^ 4078454390716387593957024 = ((8156908781432775187914048 : ℕ) : ZMod 8156908781432775187914049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8156908781432775187914049 - 1) / 3 = 2718969593810925062638016 from by norm_num]
      have h2 : (23 : ZMod 8156908781432775187914049) ^ 2718969593810925062638016 = ((6659960175084717597671277 : ℕ) : ZMod 8156908781432775187914049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8156908781432775187914049 - 1) / 7 = 1165272683061825026844864 from by norm_num]
      have h2 : (23 : ZMod 8156908781432775187914049) ^ 1165272683061825026844864 = ((5397895831279437527187793 : ℕ) : ZMod 8156908781432775187914049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8156908781432775187914049 - 1) / 907 = 8993284213266565808064 from by norm_num]
      have h2 : (23 : ZMod 8156908781432775187914049) ^ 8993284213266565808064 = ((7203703258227237651920738 : ℕ) : ZMod 8156908781432775187914049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8156908781432775187914049 - 1) / 1279 = 6377567460072537285312 from by norm_num]
      have h2 : (23 : ZMod 8156908781432775187914049) ^ 6377567460072537285312 = ((4084785522778323133092315 : ℕ) : ZMod 8156908781432775187914049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8156908781432775187914049 - 1) / 1553 = 5252355944258065156416 from by norm_num]
      have h2 : (23 : ZMod 8156908781432775187914049) ^ 5252355944258065156416 = ((4022860092823642492275042 : ℕ) : ZMod 8156908781432775187914049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8156908781432775187914049 - 1) / 53149 = 153472478907087154752 from by norm_num]
      have h2 : (23 : ZMod 8156908781432775187914049) ^ 153472478907087154752 = ((7425508567293938102039047 : ℕ) : ZMod 8156908781432775187914049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_63384337).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8156908781432775187914049 - 1) / 63384337 = 128689660056439104 from by norm_num]
      have h2 : (23 : ZMod 8156908781432775187914049) ^ 128689660056439104 = ((4400941580288635836643764 : ℕ) : ZMod 8156908781432775187914049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5062155107501579 : Nat.Prime 5062155107501579 := by
  refine lucas_primality 5062155107501579 (6 : ZMod 5062155107501579) ?_ (fun q hq hd => ?_)
  · rw [show 5062155107501579 - 1 = 5062155107501578 from by norm_num]
    reduce_mod_char
  · have e : 5062155107501579 - 1 = [2 ^ 1, 17 ^ 1, 31 ^ 1, 941 ^ 1, 15907 ^ 1, 320861 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5062155107501579 - 1) / 2 = 2531077553750789 from by norm_num]
      have h2 : (6 : ZMod 5062155107501579) ^ 2531077553750789 = ((5062155107501578 : ℕ) : ZMod 5062155107501579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5062155107501579 - 1) / 17 = 297773829853034 from by norm_num]
      have h2 : (6 : ZMod 5062155107501579) ^ 297773829853034 = ((2974549438997000 : ℕ) : ZMod 5062155107501579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5062155107501579 - 1) / 31 = 163295326048438 from by norm_num]
      have h2 : (6 : ZMod 5062155107501579) ^ 163295326048438 = ((2529414383620289 : ℕ) : ZMod 5062155107501579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5062155107501579 - 1) / 941 = 5379548467058 from by norm_num]
      have h2 : (6 : ZMod 5062155107501579) ^ 5379548467058 = ((4209402356066657 : ℕ) : ZMod 5062155107501579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5062155107501579 - 1) / 15907 = 318234431854 from by norm_num]
      have h2 : (6 : ZMod 5062155107501579) ^ 318234431854 = ((25767750133562 : ℕ) : ZMod 5062155107501579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5062155107501579 - 1) / 320861 = 15776785298 from by norm_num]
      have h2 : (6 : ZMod 5062155107501579) ^ 15776785298 = ((3186195562517993 : ℕ) : ZMod 5062155107501579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1800737447809 : Nat.Prime 1800737447809 := by
  refine lucas_primality 1800737447809 (7 : ZMod 1800737447809) ?_ (fun q hq hd => ?_)
  · rw [show 1800737447809 - 1 = 1800737447808 from by norm_num]
    reduce_mod_char
  · have e : 1800737447809 - 1 = [2 ^ 7, 3 ^ 1, 13 ^ 1, 17 ^ 1, 29 ^ 1, 31 ^ 1, 23603 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1800737447809 - 1) / 2 = 900368723904 from by norm_num]
      have h2 : (7 : ZMod 1800737447809) ^ 900368723904 = ((1800737447808 : ℕ) : ZMod 1800737447809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1800737447809 - 1) / 3 = 600245815936 from by norm_num]
      have h2 : (7 : ZMod 1800737447809) ^ 600245815936 = ((470553834733 : ℕ) : ZMod 1800737447809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1800737447809 - 1) / 13 = 138518265216 from by norm_num]
      have h2 : (7 : ZMod 1800737447809) ^ 138518265216 = ((1650192516626 : ℕ) : ZMod 1800737447809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1800737447809 - 1) / 17 = 105925732224 from by norm_num]
      have h2 : (7 : ZMod 1800737447809) ^ 105925732224 = ((442543809946 : ℕ) : ZMod 1800737447809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1800737447809 - 1) / 29 = 62094394752 from by norm_num]
      have h2 : (7 : ZMod 1800737447809) ^ 62094394752 = ((142601324377 : ℕ) : ZMod 1800737447809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1800737447809 - 1) / 31 = 58088304768 from by norm_num]
      have h2 : (7 : ZMod 1800737447809) ^ 58088304768 = ((1495772552837 : ℕ) : ZMod 1800737447809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1800737447809 - 1) / 23603 = 76292736 from by norm_num]
      have h2 : (7 : ZMod 1800737447809) ^ 76292736 = ((1501538919727 : ℕ) : ZMod 1800737447809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_81542266937 : Nat.Prime 81542266937 := by
  refine lucas_primality 81542266937 (3 : ZMod 81542266937) ?_ (fun q hq hd => ?_)
  · rw [show 81542266937 - 1 = 81542266936 from by norm_num]
    reduce_mod_char
  · have e : 81542266937 - 1 = [2 ^ 3, 13 ^ 1, 349 ^ 1, 2246591 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81542266937 - 1) / 2 = 40771133468 from by norm_num]
      have h2 : (3 : ZMod 81542266937) ^ 40771133468 = ((81542266936 : ℕ) : ZMod 81542266937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81542266937 - 1) / 13 = 6272482072 from by norm_num]
      have h2 : (3 : ZMod 81542266937) ^ 6272482072 = ((17405163007 : ℕ) : ZMod 81542266937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81542266937 - 1) / 349 = 233645464 from by norm_num]
      have h2 : (3 : ZMod 81542266937) ^ 233645464 = ((27665579281 : ℕ) : ZMod 81542266937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81542266937 - 1) / 2246591 = 36296 from by norm_num]
      have h2 : (3 : ZMod 81542266937) ^ 36296 = ((32859839283 : ℕ) : ZMod 81542266937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1201955494549698259909 : Nat.Prime 1201955494549698259909 := by
  refine lucas_primality 1201955494549698259909 (2 : ZMod 1201955494549698259909) ?_ (fun q hq hd => ?_)
  · rw [show 1201955494549698259909 - 1 = 1201955494549698259908 from by norm_num]
    reduce_mod_char
  · have e : 1201955494549698259909 - 1 = [2 ^ 2, 3 ^ 1, 31 ^ 1, 3583 ^ 1, 11059 ^ 1, 81542266937 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1201955494549698259909 - 1) / 2 = 600977747274849129954 from by norm_num]
      have h2 : (2 : ZMod 1201955494549698259909) ^ 600977747274849129954 = ((1201955494549698259908 : ℕ) : ZMod 1201955494549698259909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1201955494549698259909 - 1) / 3 = 400651831516566086636 from by norm_num]
      have h2 : (2 : ZMod 1201955494549698259909) ^ 400651831516566086636 = ((846666442417371870251 : ℕ) : ZMod 1201955494549698259909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1201955494549698259909 - 1) / 31 = 38772757888699943868 from by norm_num]
      have h2 : (2 : ZMod 1201955494549698259909) ^ 38772757888699943868 = ((712558677117553248593 : ℕ) : ZMod 1201955494549698259909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1201955494549698259909 - 1) / 3583 = 335460645980937276 from by norm_num]
      have h2 : (2 : ZMod 1201955494549698259909) ^ 335460645980937276 = ((761076195899918127427 : ℕ) : ZMod 1201955494549698259909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1201955494549698259909 - 1) / 11059 = 108685730585920812 from by norm_num]
      have h2 : (2 : ZMod 1201955494549698259909) ^ 108685730585920812 = ((581190801379882346451 : ℕ) : ZMod 1201955494549698259909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_81542266937).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1201955494549698259909 - 1) / 81542266937 = 14740275684 from by norm_num]
      have h2 : (2 : ZMod 1201955494549698259909) ^ 14740275684 = ((53625003197495577990 : ℕ) : ZMod 1201955494549698259909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_103340834172163133609939997710360109744851837737 : Nat.Prime 103340834172163133609939997710360109744851837737 := by
  refine lucas_primality 103340834172163133609939997710360109744851837737 (13 : ZMod 103340834172163133609939997710360109744851837737) ?_ (fun q hq hd => ?_)
  · rw [show 103340834172163133609939997710360109744851837737 - 1 = 103340834172163133609939997710360109744851837736 from by norm_num]
    reduce_mod_char
  · have e : 103340834172163133609939997710360109744851837737 - 1 = [2 ^ 3, 3 ^ 1, 967 ^ 1, 21023 ^ 1, 97859 ^ 1, 1800737447809 ^ 1, 1201955494549698259909 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (103340834172163133609939997710360109744851837737 - 1) / 2 = 51670417086081566804969998855180054872425918868 from by norm_num]
      have h2 : (13 : ZMod 103340834172163133609939997710360109744851837737) ^ 51670417086081566804969998855180054872425918868 = ((103340834172163133609939997710360109744851837736 : ℕ) : ZMod 103340834172163133609939997710360109744851837737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (103340834172163133609939997710360109744851837737 - 1) / 3 = 34446944724054377869979999236786703248283945912 from by norm_num]
      have h2 : (13 : ZMod 103340834172163133609939997710360109744851837737) ^ 34446944724054377869979999236786703248283945912 = ((98920287562956318804038816488304373562970226571 : ℕ) : ZMod 103340834172163133609939997710360109744851837737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (103340834172163133609939997710360109744851837737 - 1) / 967 = 106867460364181110248128229276484084534490008 from by norm_num]
      have h2 : (13 : ZMod 103340834172163133609939997710360109744851837737) ^ 106867460364181110248128229276484084534490008 = ((54436017271637491124819323522417055667261260999 : ℕ) : ZMod 103340834172163133609939997710360109744851837737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (103340834172163133609939997710360109744851837737 - 1) / 21023 = 4915608341918999838745183737352428756355032 from by norm_num]
      have h2 : (13 : ZMod 103340834172163133609939997710360109744851837737) ^ 4915608341918999838745183737352428756355032 = ((43945127826175798250073749140478328425576231497 : ℕ) : ZMod 103340834172163133609939997710360109744851837737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (103340834172163133609939997710360109744851837737 - 1) / 97859 = 1056017680255910377276898371231671177355704 from by norm_num]
      have h2 : (13 : ZMod 103340834172163133609939997710360109744851837737) ^ 1056017680255910377276898371231671177355704 = ((64595602907509741471901229662842400331364326191 : ℕ) : ZMod 103340834172163133609939997710360109744851837737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1800737447809).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (103340834172163133609939997710360109744851837737 - 1) / 1800737447809 = 57388063039340010243655431364638504 from by norm_num]
      have h2 : (13 : ZMod 103340834172163133609939997710360109744851837737) ^ 57388063039340010243655431364638504 = ((41416045332620167147881797317251644088742541681 : ℕ) : ZMod 103340834172163133609939997710360109744851837737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1201955494549698259909).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (103340834172163133609939997710360109744851837737 - 1) / 1201955494549698259909 = 85977255098683035006320904 from by norm_num]
      have h2 : (13 : ZMod 103340834172163133609939997710360109744851837737) ^ 85977255098683035006320904 = ((48225548980402529375230364663573511982795912333 : ℕ) : ZMod 103340834172163133609939997710360109744851837737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_130640501 : Nat.Prime 130640501 := by
  refine lucas_primality 130640501 (3 : ZMod 130640501) ?_ (fun q hq hd => ?_)
  · rw [show 130640501 - 1 = 130640500 from by norm_num]
    reduce_mod_char
  · have e : 130640501 - 1 = [2 ^ 2, 5 ^ 3, 261281 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (130640501 - 1) / 2 = 65320250 from by norm_num]
      have h2 : (3 : ZMod 130640501) ^ 65320250 = ((130640500 : ℕ) : ZMod 130640501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (130640501 - 1) / 5 = 26128100 from by norm_num]
      have h2 : (3 : ZMod 130640501) ^ 26128100 = ((10455409 : ℕ) : ZMod 130640501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (130640501 - 1) / 261281 = 500 from by norm_num]
      have h2 : (3 : ZMod 130640501) ^ 500 = ((45436109 : ℕ) : ZMod 130640501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_261281003 : Nat.Prime 261281003 := by
  refine lucas_primality 261281003 (2 : ZMod 261281003) ?_ (fun q hq hd => ?_)
  · rw [show 261281003 - 1 = 261281002 from by norm_num]
    reduce_mod_char
  · have e : 261281003 - 1 = [2 ^ 1, 130640501 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (261281003 - 1) / 2 = 130640501 from by norm_num]
      have h2 : (2 : ZMod 261281003) ^ 130640501 = ((261281002 : ℕ) : ZMod 261281003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_130640501).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (261281003 - 1) / 130640501 = 2 from by norm_num]
      have h2 : (2 : ZMod 261281003) ^ 2 = ((4 : ℕ) : ZMod 261281003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1365722532007 : Nat.Prime 1365722532007 := by
  refine lucas_primality 1365722532007 (6 : ZMod 1365722532007) ?_ (fun q hq hd => ?_)
  · rw [show 1365722532007 - 1 = 1365722532006 from by norm_num]
    reduce_mod_char
  · have e : 1365722532007 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 23 ^ 1, 29 ^ 1, 3793 ^ 1, 12853 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1365722532007 - 1) / 2 = 682861266003 from by norm_num]
      have h2 : (6 : ZMod 1365722532007) ^ 682861266003 = ((1365722532006 : ℕ) : ZMod 1365722532007) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1365722532007 - 1) / 3 = 455240844002 from by norm_num]
      have h2 : (6 : ZMod 1365722532007) ^ 455240844002 = ((303836314358 : ℕ) : ZMod 1365722532007) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1365722532007 - 1) / 7 = 195103218858 from by norm_num]
      have h2 : (6 : ZMod 1365722532007) ^ 195103218858 = ((761682825149 : ℕ) : ZMod 1365722532007) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1365722532007 - 1) / 23 = 59379240522 from by norm_num]
      have h2 : (6 : ZMod 1365722532007) ^ 59379240522 = ((682296549746 : ℕ) : ZMod 1365722532007) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1365722532007 - 1) / 29 = 47093880414 from by norm_num]
      have h2 : (6 : ZMod 1365722532007) ^ 47093880414 = ((1182395360120 : ℕ) : ZMod 1365722532007) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1365722532007 - 1) / 3793 = 360063942 from by norm_num]
      have h2 : (6 : ZMod 1365722532007) ^ 360063942 = ((599576520152 : ℕ) : ZMod 1365722532007) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1365722532007 - 1) / 12853 = 106257102 from by norm_num]
      have h2 : (6 : ZMod 1365722532007) ^ 106257102 = ((54524960888 : ℕ) : ZMod 1365722532007) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_133872317 : Nat.Prime 133872317 := by
  refine lucas_primality 133872317 (2 : ZMod 133872317) ?_ (fun q hq hd => ?_)
  · rw [show 133872317 - 1 = 133872316 from by norm_num]
    reduce_mod_char
  · have e : 133872317 - 1 = [2 ^ 2, 4993 ^ 1, 6703 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133872317 - 1) / 2 = 66936158 from by norm_num]
      have h2 : (2 : ZMod 133872317) ^ 66936158 = ((133872316 : ℕ) : ZMod 133872317) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133872317 - 1) / 4993 = 26812 from by norm_num]
      have h2 : (2 : ZMod 133872317) ^ 26812 = ((49668271 : ℕ) : ZMod 133872317) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133872317 - 1) / 6703 = 19972 from by norm_num]
      have h2 : (2 : ZMod 133872317) ^ 19972 = ((116038299 : ℕ) : ZMod 133872317) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1070978537 : Nat.Prime 1070978537 := by
  refine lucas_primality 1070978537 (3 : ZMod 1070978537) ?_ (fun q hq hd => ?_)
  · rw [show 1070978537 - 1 = 1070978536 from by norm_num]
    reduce_mod_char
  · have e : 1070978537 - 1 = [2 ^ 3, 133872317 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1070978537 - 1) / 2 = 535489268 from by norm_num]
      have h2 : (3 : ZMod 1070978537) ^ 535489268 = ((1070978536 : ℕ) : ZMod 1070978537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_133872317).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1070978537 - 1) / 133872317 = 8 from by norm_num]
      have h2 : (3 : ZMod 1070978537) ^ 8 = ((6561 : ℕ) : ZMod 1070978537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2238345142331 : Nat.Prime 2238345142331 := by
  refine lucas_primality 2238345142331 (2 : ZMod 2238345142331) ?_ (fun q hq hd => ?_)
  · rw [show 2238345142331 - 1 = 2238345142330 from by norm_num]
    reduce_mod_char
  · have e : 2238345142331 - 1 = [2 ^ 1, 5 ^ 1, 11 ^ 1, 19 ^ 1, 1070978537 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2238345142331 - 1) / 2 = 1119172571165 from by norm_num]
      have h2 : (2 : ZMod 2238345142331) ^ 1119172571165 = ((2238345142330 : ℕ) : ZMod 2238345142331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2238345142331 - 1) / 5 = 447669028466 from by norm_num]
      have h2 : (2 : ZMod 2238345142331) ^ 447669028466 = ((1869961065820 : ℕ) : ZMod 2238345142331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2238345142331 - 1) / 11 = 203485922030 from by norm_num]
      have h2 : (2 : ZMod 2238345142331) ^ 203485922030 = ((952652002842 : ℕ) : ZMod 2238345142331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2238345142331 - 1) / 19 = 117807639070 from by norm_num]
      have h2 : (2 : ZMod 2238345142331) ^ 117807639070 = ((163421049260 : ℕ) : ZMod 2238345142331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1070978537).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2238345142331 - 1) / 1070978537 = 2090 from by norm_num]
      have h2 : (2 : ZMod 2238345142331) ^ 2090 = ((795009448193 : ℕ) : ZMod 2238345142331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_91708751858695863542649511 : Nat.Prime 91708751858695863542649511 := by
  refine lucas_primality 91708751858695863542649511 (6 : ZMod 91708751858695863542649511) ?_ (fun q hq hd => ?_)
  · rw [show 91708751858695863542649511 - 1 = 91708751858695863542649510 from by norm_num]
    reduce_mod_char
  · have e : 91708751858695863542649511 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 1365722532007 ^ 1, 2238345142331 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91708751858695863542649511 - 1) / 2 = 45854375929347931771324755 from by norm_num]
      have h2 : (6 : ZMod 91708751858695863542649511) ^ 45854375929347931771324755 = ((91708751858695863542649510 : ℕ) : ZMod 91708751858695863542649511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91708751858695863542649511 - 1) / 3 = 30569583952898621180883170 from by norm_num]
      have h2 : (6 : ZMod 91708751858695863542649511) ^ 30569583952898621180883170 = ((54877268649984635078694731 : ℕ) : ZMod 91708751858695863542649511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91708751858695863542649511 - 1) / 5 = 18341750371739172708529902 from by norm_num]
      have h2 : (6 : ZMod 91708751858695863542649511) ^ 18341750371739172708529902 = ((10735544675965606787034795 : ℕ) : ZMod 91708751858695863542649511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1365722532007).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91708751858695863542649511 - 1) / 1365722532007 = 67150354269930 from by norm_num]
      have h2 : (6 : ZMod 91708751858695863542649511) ^ 67150354269930 = ((12716100827001232306378516 : ℕ) : ZMod 91708751858695863542649511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2238345142331).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91708751858695863542649511 - 1) / 2238345142331 = 40971675960210 from by norm_num]
      have h2 : (6 : ZMod 91708751858695863542649511) ^ 40971675960210 = ((49762331346644365366540072 : ℕ) : ZMod 91708751858695863542649511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1341858261493017491908977460646213849 : Nat.Prime 1341858261493017491908977460646213849 := by
  refine lucas_primality 1341858261493017491908977460646213849 (6 : ZMod 1341858261493017491908977460646213849) ?_ (fun q hq hd => ?_)
  · rw [show 1341858261493017491908977460646213849 - 1 = 1341858261493017491908977460646213848 from by norm_num]
    reduce_mod_char
  · have e : 1341858261493017491908977460646213849 - 1 = [2 ^ 3, 7 ^ 1, 261281003 ^ 1, 91708751858695863542649511 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1341858261493017491908977460646213849 - 1) / 2 = 670929130746508745954488730323106924 from by norm_num]
      have h2 : (6 : ZMod 1341858261493017491908977460646213849) ^ 670929130746508745954488730323106924 = ((1341858261493017491908977460646213848 : ℕ) : ZMod 1341858261493017491908977460646213849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1341858261493017491908977460646213849 - 1) / 7 = 191694037356145355986996780092316264 from by norm_num]
      have h2 : (6 : ZMod 1341858261493017491908977460646213849) ^ 191694037356145355986996780092316264 = ((1273701543818783250923302593963407095 : ℕ) : ZMod 1341858261493017491908977460646213849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_261281003).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1341858261493017491908977460646213849 - 1) / 261281003 = 5135690104086968358388372616 from by norm_num]
      have h2 : (6 : ZMod 1341858261493017491908977460646213849) ^ 5135690104086968358388372616 = ((186720000707315157853481519604056522 : ℕ) : ZMod 1341858261493017491908977460646213849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_91708751858695863542649511).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1341858261493017491908977460646213849 - 1) / 91708751858695863542649511 = 14631736168 from by norm_num]
      have h2 : (6 : ZMod 1341858261493017491908977460646213849) ^ 14631736168 = ((405661653597478594880556730848925897 : ℕ) : ZMod 1341858261493017491908977460646213849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2491229639091384610638595922517649613788649 : Nat.Prime 2491229639091384610638595922517649613788649 := by
  refine lucas_primality 2491229639091384610638595922517649613788649 (3 : ZMod 2491229639091384610638595922517649613788649) ?_ (fun q hq hd => ?_)
  · rw [show 2491229639091384610638595922517649613788649 - 1 = 2491229639091384610638595922517649613788648 from by norm_num]
    reduce_mod_char
  · have e : 2491229639091384610638595922517649613788649 - 1 = [2 ^ 3, 239 ^ 1, 971 ^ 1, 1341858261493017491908977460646213849 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2491229639091384610638595922517649613788649 - 1) / 2 = 1245614819545692305319297961258824806894324 from by norm_num]
      have h2 : (3 : ZMod 2491229639091384610638595922517649613788649) ^ 1245614819545692305319297961258824806894324 = ((2491229639091384610638595922517649613788648 : ℕ) : ZMod 2491229639091384610638595922517649613788649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2491229639091384610638595922517649613788649 - 1) / 239 = 10423554975277759877148936914299789179032 from by norm_num]
      have h2 : (3 : ZMod 2491229639091384610638595922517649613788649) ^ 10423554975277759877148936914299789179032 = ((676316256291104461737674484272807958858316 : ℕ) : ZMod 2491229639091384610638595922517649613788649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2491229639091384610638595922517649613788649 - 1) / 971 = 2565632995974649444529964904755560879288 from by norm_num]
      have h2 : (3 : ZMod 2491229639091384610638595922517649613788649) ^ 2565632995974649444529964904755560879288 = ((234750849238263330737353629206858950371756 : ℕ) : ZMod 2491229639091384610638595922517649613788649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1341858261493017491908977460646213849).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2491229639091384610638595922517649613788649 - 1) / 1341858261493017491908977460646213849 = 1856552 from by norm_num]
      have h2 : (3 : ZMod 2491229639091384610638595922517649613788649) ^ 1856552 = ((1961748987829978033835715050112183506432497 : ℕ) : ZMod 2491229639091384610638595922517649613788649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem kn_d269 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 269 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g424255915796187428893811 : 424255915796187428893811 ∈ P := S2 424255915796187428893811 prime_424255915796187428893811 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 269 = 2 ^ 256 * (2 ^ 13) from by rw [← pow_add]]; norm_num : 424255915796187428893811 ∣ 2 ^ 269 + 1).trans hd)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 424255915796187428893811 g424255915796187428893811 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d271 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 271 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1453023029482044854944519555964740294049 : 1453023029482044854944519555964740294049 ∈ P := S2 1453023029482044854944519555964740294049 prime_1453023029482044854944519555964740294049 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 271 = 2 ^ 256 * (2 ^ 15) from by rw [← pow_add]]; norm_num : 1453023029482044854944519555964740294049 ∣ 2 ^ 271 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1453023029482044854944519555964740294049 g1453023029482044854944519555964740294049 (by norm_num)

theorem kn_d311 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 311 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 : 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 ∈ P := S2 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 prime_21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 311 = 2 ^ 256 * (2 ^ 55) from by rw [← pow_add]]; norm_num : 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 ∣ 2 ^ 311 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 g21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 (by norm_num)

theorem kn_d313 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 313 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 : 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 ∈ P := S2 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 prime_5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 313 = 2 ^ 256 * (2 ^ 57) from by rw [← pow_add]]; norm_num : 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 ∣ 2 ^ 313 + 1).trans hd)
  have g21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 : 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 ∈ P := S1 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 prime_21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 (by norm_num) (hnz (by norm_num)) 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 g5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 g21705660634091537009057064062426347801694097690583490415257025927428956675122988820368249 (by norm_num)

theorem kn_d347 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 347 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 : 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 ∈ P := S2 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 prime_95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 347 = 2 ^ 256 * (2 ^ 91) from by rw [← pow_add]]; norm_num : 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 ∣ 2 ^ 347 + 1).trans hd)
  exact absurd (S3 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 g95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d353 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 353 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g3803909572078746837295094051706948091 : 3803909572078746837295094051706948091 ∈ P := S2 3803909572078746837295094051706948091 prime_3803909572078746837295094051706948091 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 353 = 2 ^ 256 * (2 ^ 97) from by rw [← pow_add]]; norm_num : 3803909572078746837295094051706948091 ∣ 2 ^ 353 + 1).trans hd)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 3803909572078746837295094051706948091 g3803909572078746837295094051706948091 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d383 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 383 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5609122817914313723820539 : 5609122817914313723820539 ∈ P := S2 5609122817914313723820539 prime_5609122817914313723820539 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 383 = 2 ^ 256 * (2 ^ 127) from by rw [← pow_add]]; norm_num : 5609122817914313723820539 ∣ 2 ^ 383 + 1).trans hd)
  have g93485380298571895397009 : 93485380298571895397009 ∈ P := S1 93485380298571895397009 prime_93485380298571895397009 (by norm_num) (hnz (by norm_num)) 5609122817914313723820539 g5609122817914313723820539 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5609122817914313723820539 g5609122817914313723820539 93485380298571895397009 g93485380298571895397009 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d401 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 401 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g18885983617 : 18885983617 ∈ P := S2 18885983617 prime_18885983617 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 401 = 2 ^ 256 * (2 ^ 145) from by rw [← pow_add]]; norm_num : 18885983617 ∣ 2 ^ 401 + 1).trans hd)
  have g3178641606717935496778334833 : 3178641606717935496778334833 ∈ P := S2 3178641606717935496778334833 prime_3178641606717935496778334833 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 401 = 2 ^ 256 * (2 ^ 145) from by rw [← pow_add]]; norm_num : 3178641606717935496778334833 ∣ 2 ^ 401 + 1).trans hd)
  have g619 : 619 ∈ P := S1 619 (by norm_num) (by norm_num) (hnz (by norm_num)) 3178641606717935496778334833 g3178641606717935496778334833 (by norm_num)
  exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 18885983617 g18885983617 619 g619 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d431 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 431 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g37452571239931 : 37452571239931 ∈ P := S2 37452571239931 prime_37452571239931 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 431 = 2 ^ 256 * (2 ^ 175) from by rw [← pow_add]]; norm_num : 37452571239931 ∣ 2 ^ 431 + 1).trans hd)
  exact S8 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 37452571239931 g37452571239931 (by norm_num)

theorem kn_d439 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 439 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g3740281 : 3740281 ∈ P := S2 3740281 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 439 = 2 ^ 256 * (2 ^ 183) from by rw [← pow_add]]; norm_num : 3740281 ∣ 2 ^ 439 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 3740281 g3740281 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d443 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 443 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g489333371 : 489333371 ∈ P := S2 489333371 prime_489333371 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 443 = 2 ^ 256 * (2 ^ 187) from by rw [← pow_add]]; norm_num : 489333371 ∣ 2 ^ 443 + 1).trans hd)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 489333371 g489333371 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d457 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 457 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6885357560205319573060633896800918448254904729193 : 6885357560205319573060633896800918448254904729193 ∈ P := S2 6885357560205319573060633896800918448254904729193 prime_6885357560205319573060633896800918448254904729193 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 457 = 2 ^ 256 * (2 ^ 201) from by rw [← pow_add]]; norm_num : 6885357560205319573060633896800918448254904729193 ∣ 2 ^ 457 + 1).trans hd)
  have g1451 : 1451 ∈ P := S1 1451 (by norm_num) (by norm_num) (hnz (by norm_num)) 6885357560205319573060633896800918448254904729193 g6885357560205319573060633896800918448254904729193 (by norm_num)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 1451 g1451 (by norm_num)

theorem kn_d461 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 461 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g110641 : 110641 ∈ P := S2 110641 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 461 = 2 ^ 256 * (2 ^ 205) from by rw [← pow_add]]; norm_num : 110641 ∣ 2 ^ 461 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 110641 g110641 (by norm_num)

theorem kn_d463 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 463 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g88119307925269041107418404833666787 : 88119307925269041107418404833666787 ∈ P := S2 88119307925269041107418404833666787 prime_88119307925269041107418404833666787 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 463 = 2 ^ 256 * (2 ^ 207) from by rw [← pow_add]]; norm_num : 88119307925269041107418404833666787 ∣ 2 ^ 463 + 1).trans hd)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 88119307925269041107418404833666787 g88119307925269041107418404833666787 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d467 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 467 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g48919673417 : 48919673417 ∈ P := S2 48919673417 prime_48919673417 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 467 = 2 ^ 256 * (2 ^ 211) from by rw [← pow_add]]; norm_num : 48919673417 ∣ 2 ^ 467 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 48919673417 g48919673417 (by norm_num)

theorem kn_d479 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 479 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g54657255048286677488033160851148008819 : 54657255048286677488033160851148008819 ∈ P := S2 54657255048286677488033160851148008819 prime_54657255048286677488033160851148008819 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 479 = 2 ^ 256 * (2 ^ 223) from by rw [← pow_add]]; norm_num : 54657255048286677488033160851148008819 ∣ 2 ^ 479 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 54657255048286677488033160851148008819 g54657255048286677488033160851148008819 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d487 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 487 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g227020551154913939039124941009 : 227020551154913939039124941009 ∈ P := S2 227020551154913939039124941009 prime_227020551154913939039124941009 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 487 = 2 ^ 256 * (2 ^ 231) from by rw [← pow_add]]; norm_num : 227020551154913939039124941009 ∣ 2 ^ 487 + 1).trans hd)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 227020551154913939039124941009 g227020551154913939039124941009 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d491 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 491 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g3563269486977651154759062020950904488457 : 3563269486977651154759062020950904488457 ∈ P := S2 3563269486977651154759062020950904488457 prime_3563269486977651154759062020950904488457 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 491 = 2 ^ 256 * (2 ^ 235) from by rw [← pow_add]]; norm_num : 3563269486977651154759062020950904488457 ∣ 2 ^ 491 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 3563269486977651154759062020950904488457 g3563269486977651154759062020950904488457 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d499 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 499 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g163673 : 163673 ∈ P := S2 163673 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 499 = 2 ^ 256 * (2 ^ 243) from by rw [← pow_add]]; norm_num : 163673 ∣ 2 ^ 499 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 163673 g163673 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d509 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 509 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g1019 : 1019 ∈ P := S2 1019 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 509 = 2 ^ 256 * (2 ^ 253) from by rw [← pow_add]]; norm_num : 1019 ∣ 2 ^ 509 + 1).trans hd)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 1019 g1019 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d521 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 521 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g90268296000189649868678102552775904610963 : 90268296000189649868678102552775904610963 ∈ P := S2 90268296000189649868678102552775904610963 prime_90268296000189649868678102552775904610963 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 521 = 2 ^ 256 * (2 ^ 256 * (2 ^ 9)) from by rw [← pow_add, ← pow_add]]; norm_num : 90268296000189649868678102552775904610963 ∣ 2 ^ 521 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 90268296000189649868678102552775904610963 g90268296000189649868678102552775904610963 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d523 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 523 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g36667531 : 36667531 ∈ P := S2 36667531 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 523 = 2 ^ 256 * (2 ^ 256 * (2 ^ 11)) from by rw [← pow_add, ← pow_add]]; norm_num : 36667531 ∣ 2 ^ 523 + 1).trans hd)
  have g129175771 : 129175771 ∈ P := S2 129175771 prime_129175771 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 523 = 2 ^ 256 * (2 ^ 256 * (2 ^ 11)) from by rw [← pow_add, ← pow_add]]; norm_num : 129175771 ∣ 2 ^ 523 + 1).trans hd)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 36667531 g36667531 129175771 g129175771 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d541 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 541 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g86561 : 86561 ∈ P := S2 86561 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 541 = 2 ^ 256 * (2 ^ 256 * (2 ^ 29)) from by rw [← pow_add, ← pow_add]]; norm_num : 86561 ∣ 2 ^ 541 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 86561 g86561 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d547 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 547 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1533926272849 : 1533926272849 ∈ P := S2 1533926272849 prime_1533926272849 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 547 = 2 ^ 256 * (2 ^ 256 * (2 ^ 35)) from by rw [← pow_add, ← pow_add]]; norm_num : 1533926272849 ∣ 2 ^ 547 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1533926272849 g1533926272849 (by norm_num)

theorem kn_d557 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 557 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g124769 : 124769 ∈ P := S2 124769 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 557 = 2 ^ 256 * (2 ^ 256 * (2 ^ 45)) from by rw [← pow_add, ← pow_add]]; norm_num : 124769 ∣ 2 ^ 557 + 1).trans hd)
  have g4159 : 4159 ∈ P := S1 4159 (by norm_num) (by norm_num) (hnz (by norm_num)) 124769 g124769 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 124769 g124769 4159 g4159 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d563 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 563 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g74906924194076922022321 : 74906924194076922022321 ∈ P := S2 74906924194076922022321 prime_74906924194076922022321 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 563 = 2 ^ 256 * (2 ^ 256 * (2 ^ 51)) from by rw [← pow_add, ← pow_add]]; norm_num : 74906924194076922022321 ∣ 2 ^ 563 + 1).trans hd)
  have g499 : 499 ∈ P := S1 499 (by norm_num) (by norm_num) (hnz (by norm_num)) 74906924194076922022321 g74906924194076922022321 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 499 g499 (by norm_num)

theorem kn_d569 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 569 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g2058017388830521 : 2058017388830521 ∈ P := S2 2058017388830521 prime_2058017388830521 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 569 = 2 ^ 256 * (2 ^ 256 * (2 ^ 57)) from by rw [← pow_add, ← pow_add]]; norm_num : 2058017388830521 ∣ 2 ^ 569 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 2058017388830521 g2058017388830521 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d571 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 571 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g73205584889 : 73205584889 ∈ P := S2 73205584889 prime_73205584889 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 571 = 2 ^ 256 * (2 ^ 256 * (2 ^ 59)) from by rw [← pow_add, ← pow_add]]; norm_num : 73205584889 ∣ 2 ^ 571 + 1).trans hd)
  exact S8 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 73205584889 g73205584889 (by norm_num)

theorem kn_d577 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 577 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g75011 : 75011 ∈ P := S2 75011 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 577 = 2 ^ 256 * (2 ^ 256 * (2 ^ 65)) from by rw [← pow_add, ← pow_add]]; norm_num : 75011 ∣ 2 ^ 577 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 75011 g75011 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d587 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 587 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g13119770765051463547 : 13119770765051463547 ∈ P := S2 13119770765051463547 prime_13119770765051463547 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 587 = 2 ^ 256 * (2 ^ 256 * (2 ^ 75)) from by rw [← pow_add, ← pow_add]]; norm_num : 13119770765051463547 ∣ 2 ^ 587 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 13119770765051463547 g13119770765051463547 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d593 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 593 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1187 : 1187 ∈ P := S2 1187 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 593 = 2 ^ 256 * (2 ^ 256 * (2 ^ 81)) from by rw [← pow_add, ← pow_add]]; norm_num : 1187 ∣ 2 ^ 593 + 1).trans hd)
  have g6975729612775483517844546731 : 6975729612775483517844546731 ∈ P := S2 6975729612775483517844546731 prime_6975729612775483517844546731 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 593 = 2 ^ 256 * (2 ^ 256 * (2 ^ 81)) from by rw [← pow_add, ← pow_add]]; norm_num : 6975729612775483517844546731 ∣ 2 ^ 593 + 1).trans hd)
  have g23143 : 23143 ∈ P := S1 23143 (by norm_num) (by norm_num) (hnz (by norm_num)) 6975729612775483517844546731 g6975729612775483517844546731 (by norm_num)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 1187 g1187 23143 g23143 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d599 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 599 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g366994123 : 366994123 ∈ P := S2 366994123 prime_366994123 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 599 = 2 ^ 256 * (2 ^ 256 * (2 ^ 87)) from by rw [← pow_add, ← pow_add]]; norm_num : 366994123 ∣ 2 ^ 599 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 366994123 g366994123 (by norm_num)

theorem kn_d601 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 601 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g9293424294571360217 : 9293424294571360217 ∈ P := S2 9293424294571360217 prime_9293424294571360217 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 601 = 2 ^ 256 * (2 ^ 256 * (2 ^ 89)) from by rw [← pow_add, ← pow_add]]; norm_num : 9293424294571360217 ∣ 2 ^ 601 + 1).trans hd)
  exact S8 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 9293424294571360217 g9293424294571360217 (by norm_num)

theorem kn_d607 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 607 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g115331 : 115331 ∈ P := S2 115331 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 607 = 2 ^ 256 * (2 ^ 256 * (2 ^ 95)) from by rw [← pow_add, ← pow_add]]; norm_num : 115331 ∣ 2 ^ 607 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 115331 g115331 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d641 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 641 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1078163 : 1078163 ∈ P := S2 1078163 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 641 = 2 ^ 256 * (2 ^ 256 * (2 ^ 129)) from by rw [← pow_add, ← pow_add]]; norm_num : 1078163 ∣ 2 ^ 641 + 1).trans hd)
  exact S8 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 1078163 g1078163 (by norm_num)

theorem kn_d643 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 643 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g1081756861144651 : 1081756861144651 ∈ P := S2 1081756861144651 prime_1081756861144651 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 643 = 2 ^ 256 * (2 ^ 256 * (2 ^ 131)) from by rw [← pow_add, ← pow_add]]; norm_num : 1081756861144651 ∣ 2 ^ 643 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 1081756861144651 g1081756861144651 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d647 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 647 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4570409 : 4570409 ∈ P := S2 4570409 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 647 = 2 ^ 256 * (2 ^ 256 * (2 ^ 135)) from by rw [← pow_add, ← pow_add]]; norm_num : 4570409 ∣ 2 ^ 647 + 1).trans hd)
  have g9021769 : 9021769 ∈ P := S2 9021769 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 647 = 2 ^ 256 * (2 ^ 256 * (2 ^ 135)) from by rw [← pow_add, ← pow_add]]; norm_num : 9021769 ∣ 2 ^ 647 + 1).trans hd)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4570409 g4570409 9021769 g9021769 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d653 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 653 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1307 : 1307 ∈ P := S2 1307 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 653 = 2 ^ 256 * (2 ^ 256 * (2 ^ 141)) from by rw [← pow_add, ← pow_add]]; norm_num : 1307 ∣ 2 ^ 653 + 1).trans hd)
  have g12550478467 : 12550478467 ∈ P := S2 12550478467 prime_12550478467 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 653 = 2 ^ 256 * (2 ^ 256 * (2 ^ 141)) from by rw [← pow_add, ← pow_add]]; norm_num : 12550478467 ∣ 2 ^ 653 + 1).trans hd)
  have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 1307 g1307 (by norm_num)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 12550478467 g12550478467 109 g109 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d659 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 659 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g284689 : 284689 ∈ P := S2 284689 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 659 = 2 ^ 256 * (2 ^ 256 * (2 ^ 147)) from by rw [← pow_add, ← pow_add]]; norm_num : 284689 ∣ 2 ^ 659 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 284689 g284689 (by norm_num)

theorem kn_d661 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 661 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g206233 : 206233 ∈ P := S2 206233 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 661 = 2 ^ 256 * (2 ^ 256 * (2 ^ 149)) from by rw [← pow_add, ← pow_add]]; norm_num : 206233 ∣ 2 ^ 661 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 206233 g206233 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d673 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 673 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4061132942857 : 4061132942857 ∈ P := S2 4061132942857 prime_4061132942857 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 673 = 2 ^ 256 * (2 ^ 256 * (2 ^ 161)) from by rw [← pow_add, ← pow_add]]; norm_num : 4061132942857 ∣ 2 ^ 673 + 1).trans hd)
  exact S6 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 4061132942857 g4061132942857 (by norm_num)

theorem kn_d677 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 677 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2920579 : 2920579 ∈ P := S2 2920579 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 677 = 2 ^ 256 * (2 ^ 256 * (2 ^ 165)) from by rw [← pow_add, ← pow_add]]; norm_num : 2920579 ∣ 2 ^ 677 + 1).trans hd)
  have g6190489 : 6190489 ∈ P := S2 6190489 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 677 = 2 ^ 256 * (2 ^ 256 * (2 ^ 165)) from by rw [← pow_add, ← pow_add]]; norm_num : 6190489 ∣ 2 ^ 677 + 1).trans hd)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2920579 g2920579 6190489 g6190489 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d683 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 683 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1676083 : 1676083 ∈ P := S2 1676083 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 683 = 2 ^ 256 * (2 ^ 256 * (2 ^ 171)) from by rw [← pow_add, ← pow_add]]; norm_num : 1676083 ∣ 2 ^ 683 + 1).trans hd)
  have g14449 : 14449 ∈ P := S1 14449 (by norm_num) (by norm_num) (hnz (by norm_num)) 1676083 g1676083 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 14449 g14449 (by norm_num)

theorem kn_d691 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 691 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4668478921 : 4668478921 ∈ P := S2 4668478921 prime_4668478921 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 691 = 2 ^ 256 * (2 ^ 256 * (2 ^ 179)) from by rw [← pow_add, ← pow_add]]; norm_num : 4668478921 ∣ 2 ^ 691 + 1).trans hd)
  exact S6 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 4668478921 g4668478921 (by norm_num)

theorem kn_d709 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 709 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g5045586197318561 : 5045586197318561 ∈ P := S2 5045586197318561 prime_5045586197318561 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 709 = 2 ^ 256 * (2 ^ 256 * (2 ^ 197)) from by rw [← pow_add, ← pow_add]]; norm_num : 5045586197318561 ∣ 2 ^ 709 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 5045586197318561 g5045586197318561 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d719 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 719 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4900402101963269918180361130213343099 : 4900402101963269918180361130213343099 ∈ P := S2 4900402101963269918180361130213343099 prime_4900402101963269918180361130213343099 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 719 = 2 ^ 256 * (2 ^ 256 * (2 ^ 207)) from by rw [← pow_add, ← pow_add]]; norm_num : 4900402101963269918180361130213343099 ∣ 2 ^ 719 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4900402101963269918180361130213343099 g4900402101963269918180361130213343099 (by norm_num)

theorem kn_d727 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 727 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g11633 : 11633 ∈ P := S2 11633 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 727 = 2 ^ 256 * (2 ^ 256 * (2 ^ 215)) from by rw [← pow_add, ← pow_add]]; norm_num : 11633 ∣ 2 ^ 727 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 11633 g11633 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d733 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 733 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g15044222650915986784475012020785853019343366205331 : 15044222650915986784475012020785853019343366205331 ∈ P := S2 15044222650915986784475012020785853019343366205331 prime_15044222650915986784475012020785853019343366205331 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 733 = 2 ^ 256 * (2 ^ 256 * (2 ^ 221)) from by rw [← pow_add, ← pow_add]]; norm_num : 15044222650915986784475012020785853019343366205331 ∣ 2 ^ 733 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 15044222650915986784475012020785853019343366205331 g15044222650915986784475012020785853019343366205331 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d743 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 743 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4343579 : 4343579 ∈ P := S2 4343579 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 743 = 2 ^ 256 * (2 ^ 256 * (2 ^ 231)) from by rw [← pow_add, ← pow_add]]; norm_num : 4343579 ∣ 2 ^ 743 + 1).trans hd)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 4343579 g4343579 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4343579 g4343579 59 g59 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d757 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 757 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g417817067 : 417817067 ∈ P := S2 417817067 prime_417817067 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 757 = 2 ^ 256 * (2 ^ 256 * (2 ^ 245)) from by rw [← pow_add, ← pow_add]]; norm_num : 417817067 ∣ 2 ^ 757 + 1).trans hd)
  exact S6 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 417817067 g417817067 (by norm_num)

theorem kn_d761 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 761 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1485778288798957523 : 1485778288798957523 ∈ P := S2 1485778288798957523 prime_1485778288798957523 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 761 = 2 ^ 256 * (2 ^ 256 * (2 ^ 249)) from by rw [← pow_add, ← pow_add]]; norm_num : 1485778288798957523 ∣ 2 ^ 761 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1485778288798957523 g1485778288798957523 (by norm_num)

theorem kn_d769 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 769 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g86369467 : 86369467 ∈ P := S2 86369467 prime_86369467 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 769 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 1))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 86369467 ∣ 2 ^ 769 + 1).trans hd)
  exact absurd (S3 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 86369467 g86369467 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d773 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 773 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g533371 : 533371 ∈ P := S2 533371 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 773 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 5))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 533371 ∣ 2 ^ 773 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 533371 g533371 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d787 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 787 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5405369360996178738798259049 : 5405369360996178738798259049 ∈ P := S2 5405369360996178738798259049 prime_5405369360996178738798259049 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 787 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 19))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5405369360996178738798259049 ∣ 2 ^ 787 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5405369360996178738798259049 g5405369360996178738798259049 (by norm_num)

theorem kn_d797 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 797 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g875107 : 875107 ∈ P := S2 875107 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 797 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 29))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 875107 ∣ 2 ^ 797 + 1).trans hd)
  have g16829 : 16829 ∈ P := S1 16829 (by norm_num) (by norm_num) (hnz (by norm_num)) 875107 g875107 (by norm_num)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 16829 g16829 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d809 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 809 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g14563 : 14563 ∈ P := S2 14563 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 809 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 41))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 14563 ∣ 2 ^ 809 + 1).trans hd)
  exact absurd (S3 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 14563 g14563 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d821 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 821 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6569 : 6569 ∈ P := S2 6569 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 821 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 53))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 6569 ∣ 2 ^ 821 + 1).trans hd)
  have g1037866321911576169081957409 : 1037866321911576169081957409 ∈ P := S2 1037866321911576169081957409 prime_1037866321911576169081957409 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 821 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 53))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 1037866321911576169081957409 ∣ 2 ^ 821 + 1).trans hd)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 6569 g6569 1037866321911576169081957409 g1037866321911576169081957409 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d823 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 823 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g13615553872073 : 13615553872073 ∈ P := S2 13615553872073 prime_13615553872073 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 823 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 55))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 13615553872073 ∣ 2 ^ 823 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 13615553872073 g13615553872073 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d829 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 829 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g131147801 : 131147801 ∈ P := S2 131147801 prime_131147801 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 829 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 61))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 131147801 ∣ 2 ^ 829 + 1).trans hd)
  exact absurd (S3 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 131147801 g131147801 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d839 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 839 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g1377062372371126895706481139 : 1377062372371126895706481139 ∈ P := S2 1377062372371126895706481139 prime_1377062372371126895706481139 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 839 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 71))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 1377062372371126895706481139 ∣ 2 ^ 839 + 1).trans hd)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 1377062372371126895706481139 g1377062372371126895706481139 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d857 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 857 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g252182368360125289180898199073630970779 : 252182368360125289180898199073630970779 ∈ P := S2 252182368360125289180898199073630970779 prime_252182368360125289180898199073630970779 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 857 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 89))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 252182368360125289180898199073630970779 ∣ 2 ^ 857 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 252182368360125289180898199073630970779 g252182368360125289180898199073630970779 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d859 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 859 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g267946153 : 267946153 ∈ P := S2 267946153 prime_267946153 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 859 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 91))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 267946153 ∣ 2 ^ 859 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 267946153 g267946153 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d877 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 877 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g29819 : 29819 ∈ P := S2 29819 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 877 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 109))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 29819 ∣ 2 ^ 877 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 29819 g29819 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d881 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 881 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g42295049 : 42295049 ∈ P := S2 42295049 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 881 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 113))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 42295049 ∣ 2 ^ 881 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 42295049 g42295049 (by norm_num)

theorem kn_d887 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 887 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5323 : 5323 ∈ P := S2 5323 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 887 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 119))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5323 ∣ 2 ^ 887 + 1).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 5323 g5323 (by norm_num)

theorem kn_d907 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 907 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8156908781432775187914049 : 8156908781432775187914049 ∈ P := S2 8156908781432775187914049 prime_8156908781432775187914049 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 907 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 139))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 8156908781432775187914049 ∣ 2 ^ 907 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 8156908781432775187914049 g8156908781432775187914049 (by norm_num)

theorem kn_d919 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 919 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g14968673 : 14968673 ∈ P := S2 14968673 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 919 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 151))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 14968673 ∣ 2 ^ 919 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 14968673 g14968673 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d929 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 929 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8243947 : 8243947 ∈ P := S2 8243947 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 929 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 161))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 8243947 ∣ 2 ^ 929 + 1).trans hd)
  exact S8 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 8243947 g8243947 (by norm_num)

theorem kn_d941 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 941 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5062155107501579 : 5062155107501579 ∈ P := S2 5062155107501579 prime_5062155107501579 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 941 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 173))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5062155107501579 ∣ 2 ^ 941 + 1).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 5062155107501579 g5062155107501579 (by norm_num)

theorem kn_d947 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 947 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g13259 : 13259 ∈ P := S2 13259 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 947 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 179))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 13259 ∣ 2 ^ 947 + 1).trans hd)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 13259 g13259 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d967 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 967 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g103340834172163133609939997710360109744851837737 : 103340834172163133609939997710360109744851837737 ∈ P := S2 103340834172163133609939997710360109744851837737 prime_103340834172163133609939997710360109744851837737 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 967 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 199))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 103340834172163133609939997710360109744851837737 ∣ 2 ^ 967 + 1).trans hd)
  exact absurd (S3 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 103340834172163133609939997710360109744851837737 g103340834172163133609939997710360109744851837737 (by norm_num) (by norm_num)) (by norm_num)

theorem kn_d971 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 971 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2491229639091384610638595922517649613788649 : 2491229639091384610638595922517649613788649 ∈ P := S2 2491229639091384610638595922517649613788649 prime_2491229639091384610638595922517649613788649 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 971 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 203))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 2491229639091384610638595922517649613788649 ∣ 2 ^ 971 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2491229639091384610638595922517649613788649 g2491229639091384610638595922517649613788649 (by norm_num)

theorem kn_d991 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 991 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g3060209 : 3060209 ∈ P := S2 3060209 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 991 = 2 ^ 256 * (2 ^ 256 * (2 ^ 256 * (2 ^ 223))) from by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 3060209 ∣ 2 ^ 991 + 1).trans hd)
  exact absurd (S3 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 3060209 g3060209 (by norm_num) (by norm_num)) (by norm_num)

-- Section 2. The new sieve.

set_option maxHeartbeats 4000000 in
theorem nsieve_0 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p) :
    ∀ d ∈ ({269, 271, 311, 313, 347, 353, 383, 401, 431, 439, 443, 457, 461, 463, 467, 479, 487, 491, 499, 509, 521, 523, 541, 547, 557} : Finset ℕ), m % (2 * d) ≠ d := by
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kn_d269 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d271 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d311 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d313 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d347 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d353 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d383 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d401 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d431 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d439 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d443 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d457 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d461 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d463 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d467 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d479 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d487 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d491 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d499 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d509 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d521 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d523 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d541 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d547 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d557 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)

set_option maxHeartbeats 4000000 in
theorem nsieve_1 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p) :
    ∀ d ∈ ({563, 569, 571, 577, 587, 593, 599, 601, 607, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 709, 719, 727, 733, 743, 757} : Finset ℕ), m % (2 * d) ≠ d := by
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kn_d563 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d569 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d571 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d577 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d587 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d593 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d599 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d601 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d607 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d641 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d643 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d647 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d653 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d659 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d661 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d673 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d677 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d683 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d691 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d709 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d719 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d727 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d733 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d743 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d757 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)

set_option maxHeartbeats 4000000 in
theorem nsieve_2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p) :
    ∀ d ∈ ({761, 769, 773, 787, 797, 809, 821, 823, 829, 839, 857, 859, 877, 881, 887, 907, 919, 929, 941, 947, 967, 971, 991} : Finset ℕ), m % (2 * d) ≠ d := by
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kn_d761 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d769 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d773 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d787 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d797 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d809 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d821 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d823 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d829 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d839 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d857 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d859 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d877 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d881 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d887 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d907 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d919 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d929 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d941 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d947 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d967 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d971 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)
  · exact kn_d991 hP h3P E (two_pow_add_one_dvd_of_odd_mul h)

set_option maxHeartbeats 4000000 in
theorem nsieve {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p) :
    ∀ d ∈ ({269, 271, 311, 313, 347, 353, 383, 401, 431, 439, 443, 457, 461, 463, 467, 479, 487, 491, 499, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 709, 719, 727, 733, 743, 757, 761, 769, 773, 787, 797, 809, 821, 823, 829, 839, 857, 859, 877, 881, 887, 907, 919, 929, 941, 947, 967, 971, 991} : Finset ℕ), m % (2 * d) ≠ d := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nsieve_0 hP h3P E 269 (by simp)
  · exact nsieve_0 hP h3P E 271 (by simp)
  · exact nsieve_0 hP h3P E 311 (by simp)
  · exact nsieve_0 hP h3P E 313 (by simp)
  · exact nsieve_0 hP h3P E 347 (by simp)
  · exact nsieve_0 hP h3P E 353 (by simp)
  · exact nsieve_0 hP h3P E 383 (by simp)
  · exact nsieve_0 hP h3P E 401 (by simp)
  · exact nsieve_0 hP h3P E 431 (by simp)
  · exact nsieve_0 hP h3P E 439 (by simp)
  · exact nsieve_0 hP h3P E 443 (by simp)
  · exact nsieve_0 hP h3P E 457 (by simp)
  · exact nsieve_0 hP h3P E 461 (by simp)
  · exact nsieve_0 hP h3P E 463 (by simp)
  · exact nsieve_0 hP h3P E 467 (by simp)
  · exact nsieve_0 hP h3P E 479 (by simp)
  · exact nsieve_0 hP h3P E 487 (by simp)
  · exact nsieve_0 hP h3P E 491 (by simp)
  · exact nsieve_0 hP h3P E 499 (by simp)
  · exact nsieve_0 hP h3P E 509 (by simp)
  · exact nsieve_0 hP h3P E 521 (by simp)
  · exact nsieve_0 hP h3P E 523 (by simp)
  · exact nsieve_0 hP h3P E 541 (by simp)
  · exact nsieve_0 hP h3P E 547 (by simp)
  · exact nsieve_0 hP h3P E 557 (by simp)
  · exact nsieve_1 hP h3P E 563 (by simp)
  · exact nsieve_1 hP h3P E 569 (by simp)
  · exact nsieve_1 hP h3P E 571 (by simp)
  · exact nsieve_1 hP h3P E 577 (by simp)
  · exact nsieve_1 hP h3P E 587 (by simp)
  · exact nsieve_1 hP h3P E 593 (by simp)
  · exact nsieve_1 hP h3P E 599 (by simp)
  · exact nsieve_1 hP h3P E 601 (by simp)
  · exact nsieve_1 hP h3P E 607 (by simp)
  · exact nsieve_1 hP h3P E 641 (by simp)
  · exact nsieve_1 hP h3P E 643 (by simp)
  · exact nsieve_1 hP h3P E 647 (by simp)
  · exact nsieve_1 hP h3P E 653 (by simp)
  · exact nsieve_1 hP h3P E 659 (by simp)
  · exact nsieve_1 hP h3P E 661 (by simp)
  · exact nsieve_1 hP h3P E 673 (by simp)
  · exact nsieve_1 hP h3P E 677 (by simp)
  · exact nsieve_1 hP h3P E 683 (by simp)
  · exact nsieve_1 hP h3P E 691 (by simp)
  · exact nsieve_1 hP h3P E 709 (by simp)
  · exact nsieve_1 hP h3P E 719 (by simp)
  · exact nsieve_1 hP h3P E 727 (by simp)
  · exact nsieve_1 hP h3P E 733 (by simp)
  · exact nsieve_1 hP h3P E 743 (by simp)
  · exact nsieve_1 hP h3P E 757 (by simp)
  · exact nsieve_2 hP h3P E 761 (by simp)
  · exact nsieve_2 hP h3P E 769 (by simp)
  · exact nsieve_2 hP h3P E 773 (by simp)
  · exact nsieve_2 hP h3P E 787 (by simp)
  · exact nsieve_2 hP h3P E 797 (by simp)
  · exact nsieve_2 hP h3P E 809 (by simp)
  · exact nsieve_2 hP h3P E 821 (by simp)
  · exact nsieve_2 hP h3P E 823 (by simp)
  · exact nsieve_2 hP h3P E 829 (by simp)
  · exact nsieve_2 hP h3P E 839 (by simp)
  · exact nsieve_2 hP h3P E 857 (by simp)
  · exact nsieve_2 hP h3P E 859 (by simp)
  · exact nsieve_2 hP h3P E 877 (by simp)
  · exact nsieve_2 hP h3P E 881 (by simp)
  · exact nsieve_2 hP h3P E 887 (by simp)
  · exact nsieve_2 hP h3P E 907 (by simp)
  · exact nsieve_2 hP h3P E 919 (by simp)
  · exact nsieve_2 hP h3P E 929 (by simp)
  · exact nsieve_2 hP h3P E 941 (by simp)
  · exact nsieve_2 hP h3P E 947 (by simp)
  · exact nsieve_2 hP h3P E 967 (by simp)
  · exact nsieve_2 hP h3P E 971 (by simp)
  · exact nsieve_2 hP h3P E 991 (by simp)

-- Section 3. The step.

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨A1 + A2, fun n h hiff he ha hlow hs1 hcnt => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he' =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he'⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have hfa : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by simp
  rw [he] at E
  have hns := nsieve hP h3P E
  rw [hfa] at hns
  by_cases hsm : 3 ∣ padicValNat 2 n ∨ 5 ∣ padicValNat 2 n ∨ 7 ∣ padicValNat 2 n ∨
      11 ∣ padicValNat 2 n ∨ 13 ∣ padicValNat 2 n
  · have := h1 n h hiff he ha hlow hs1 hcnt hns hsm
    omega
  · simp only [not_or] at hsm
    obtain ⟨n3, n5, n7, n11, n13⟩ := hsm
    have := h2 n h hiff he ha hlow hs1 hcnt hns n3 n5 n7 n11 n13
    omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H1_R1
