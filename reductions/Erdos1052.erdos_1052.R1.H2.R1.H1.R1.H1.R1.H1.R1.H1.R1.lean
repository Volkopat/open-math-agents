import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H1.R1.H1.R1
-- Upstream path: reductions/Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H1.R1.H1.R1.lean
-- Credit: @adammcarter (agent: Claude Code, model claude-fable-5-2)
--
-- Splits step H1 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H1.R1 (3 is the only repeated odd prime of the
-- unitary perfect number n, its exponent is 5, a = padicValNat 2 n >= 262 lies outside the classes
-- excluded there) by the power of 2 dividing a, with a longer list of excluded classes built in.
-- Proving H1, H2 and H3 proves the step.
--
-- Notation as in the parent file: a is an ODD MULTIPLE of d when a mod 2d = d; then 2^d + 1 divides
-- 2^a + 1.  Balance equation: (2^a + 1)(3^5 + 1) prod (p + 1) = 2^(a+1) 3^5 prod p over the simple primes p.
--
-- PROVED BELOW (no hypothesis needed):
--   sieve_odd:  a is no odd multiple of any of 238 odd values d, 263 <= d <= 3167.
--   sieve_even: a is no odd multiple of any of 249 even values d, 262 <= d <= 2972.
--   Method (forced roots, as in the parent): known primes q of 2^d + 1 are simple primes of n,
--   the odd primes other than 3 of q + 1 are simple again, and the chain ends in a prime with two
--   sources (290 values of d), a square (137), or more than 5 factors of 3 on the left (60).
--   The comment on each case names the contradiction.  Primes above 4.3 * 10^7 carry a Lucas
--   certificate (theorems prime_<p>, 41 of them).
--   The lists hold the values found this way that are not odd multiples of an earlier excluded
--   value; values of d in the same range that are missing are either covered by a smaller one or
--   had no usable small prime factor (they stay open).
--   main: the parent conditions give v2(a) in {0, 1, 2, 3} or 2^20 | a.
--
-- H1 (OPEN): a odd.          H2 (OPEN): a even, 16 does not divide a.
-- H3 (OPEN): 2^20 = 1048576 divides a (no class of the lists applies there).
-- No known unitary perfect number satisfies the hypotheses of the step.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1 hiding H1 H2 main

-- H1: a is bounded when a is odd.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 →
    262 ≤ padicValNat 2 n → padicValNat 2 n % 2 = 1 →
    (∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → padicValNat 2 n % (2 * d) ≠ d) →
    ((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 4 →
    (∀ d ∈ (({263, 277, 281, 283, 293, 307, 317, 331, 337, 349, 359, 367, 379, 389, 397, 401, 431, 433, 439,
      443, 449, 461, 467, 479, 499, 521, 523, 541, 547, 557, 569, 571, 577, 587, 599, 607, 631,
      641, 647, 659, 661, 677, 683, 709, 727, 743, 751, 787, 797, 807} : Finset ℕ) ∪
      ({809, 813, 821, 823, 853, 859, 881, 883, 887, 919, 929, 933, 937, 941, 947, 953, 967, 971, 977,
      991, 997, 1009, 1013, 1021, 1041, 1049, 1093, 1097, 1119, 1151, 1153, 1171, 1181, 1193,
      1223, 1227, 1237, 1249, 1257, 1263, 1277, 1279, 1283, 1289, 1291, 1307, 1319, 1327, 1345,
      1355} : Finset ℕ) ∪
      ({1361, 1367, 1399, 1427, 1439, 1451, 1461, 1481, 1483, 1487, 1493, 1499, 1509, 1527, 1531, 1555,
      1559, 1565, 1567, 1571, 1579, 1601, 1609, 1613, 1621, 1627, 1699, 1721, 1733, 1735, 1759,
      1765, 1779, 1789, 1803, 1823, 1839, 1857, 1865, 1871, 1897, 1901, 1915, 1933, 1949, 1973,
      1979, 2017, 2027, 2029} : Finset ℕ) ∪
      ({2045, 2069, 2081, 2095, 2099, 2103, 2105, 2129, 2153, 2157, 2177, 2191, 2199, 2217, 2221, 2237,
      2239, 2243, 2251, 2269, 2271, 2273, 2281, 2285, 2293, 2307, 2333, 2341, 2347, 2357, 2383,
      2399, 2435, 2441, 2447, 2471, 2477, 2503, 2517, 2543, 2545, 2549, 2571, 2579, 2589, 2593,
      2609, 2611, 2631, 2647} : Finset ℕ) ∪
      ({2689, 2693, 2699, 2707, 2711, 2719, 2721, 2733, 2741, 2753, 2817, 2819, 2837, 2851, 2863, 2903,
      2927, 2939, 2947, 2949, 2953, 2957, 2959, 2965, 2969, 2981, 2999, 3005, 3037, 3061, 3065,
      3067, 3089, 3093, 3117, 3121, 3137, 3167} : Finset ℕ)),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H2: a is bounded when a is even and 16 does not divide a.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 →
    262 ≤ padicValNat 2 n → padicValNat 2 n % 2 = 0 → padicValNat 2 n % 16 ≠ 0 →
    (∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ (({262, 268, 274, 278, 284, 296, 298, 302, 314, 316, 326, 328, 334, 344, 346, 358, 362, 376, 382,
      386, 388, 394, 398, 412, 422, 428, 436, 446, 452, 454, 458, 466, 478, 482, 502, 508, 514,
      526, 536, 538, 542, 548, 554, 562, 568, 586, 604, 614, 622, 626} : Finset ℕ) ∪
      ({628, 632, 634, 652, 662, 674, 694, 698, 712, 718, 724, 758, 766, 776, 778, 788, 794, 802, 808,
      818, 824, 838, 842, 856, 862, 866, 878, 892, 898, 904, 908, 914, 922, 932, 934, 958, 974,
      982, 998, 1006, 1018, 1042, 1046, 1048, 1076, 1082, 1084, 1108, 1126, 1138} : Finset ℕ) ∪
      ({1142, 1154, 1172, 1174, 1198, 1202, 1226, 1234, 1238, 1262, 1294, 1304, 1318, 1324, 1346, 1382,
      1384, 1388, 1396, 1418, 1432, 1438, 1454, 1466, 1468, 1478, 1492, 1502, 1522, 1528, 1544,
      1546, 1574, 1604, 1618, 1622, 1636, 1646, 1654, 1678, 1688, 1698, 1706, 1718, 1726, 1754,
      1756, 1762, 1766, 1784} : Finset ℕ) ∪
      ({1796, 1816, 1822, 1838, 1844, 1858, 1864, 1868, 1874, 1882, 1894, 1912, 1934, 1942, 1982, 1994,
      2018, 2026, 2038, 2056, 2062, 2066, 2098, 2102, 2104, 2126, 2138, 2168, 2174, 2182, 2186,
      2188, 2194, 2206, 2216, 2218, 2234, 2238, 2246, 2284, 2302, 2306, 2308, 2326, 2342, 2348,
      2362, 2372, 2374, 2396} : Finset ℕ) ∪
      ({2402, 2428, 2434, 2446, 2458, 2462, 2468, 2474, 2498, 2518, 2524, 2536, 2554, 2564, 2566, 2572,
      2578, 2582, 2594, 2602, 2606, 2612, 2614, 2636, 2638, 2644, 2648, 2654, 2692, 2722, 2734,
      2762, 2764, 2778, 2798, 2818, 2824, 2846, 2854, 2858, 2878, 2902, 2906, 2908, 2932, 2942,
      2962, 2966, 2972} : Finset ℕ)),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H3: a is bounded when 2^20 divides a.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 →
    1048576 ∣ padicValNat 2 n →
    padicValNat 2 n ≤ A

-- Section 1. The sieve.

theorem prime_25792643401363 : Nat.Prime 25792643401363 := by
  refine lucas_primality 25792643401363 (3 : ZMod 25792643401363) ?_ (fun q hq hd => ?_)
  · rw [show 25792643401363 - 1 = 25792643401362 from by norm_num]
    reduce_mod_char
  · have e : 25792643401363 - 1 = [2 ^ 1, 3 ^ 2, 67 ^ 1, 277 ^ 1, 4703 ^ 1, 16417 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25792643401363 - 1) / 2 = 12896321700681 from by norm_num]
      have h2 : (3 : ZMod 25792643401363) ^ 12896321700681 = ((25792643401362 : ℕ) : ZMod 25792643401363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25792643401363 - 1) / 3 = 8597547800454 from by norm_num]
      have h2 : (3 : ZMod 25792643401363) ^ 8597547800454 = ((2082476935352 : ℕ) : ZMod 25792643401363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25792643401363 - 1) / 67 = 384964826886 from by norm_num]
      have h2 : (3 : ZMod 25792643401363) ^ 384964826886 = ((10911884704240 : ℕ) : ZMod 25792643401363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25792643401363 - 1) / 277 = 93114236106 from by norm_num]
      have h2 : (3 : ZMod 25792643401363) ^ 93114236106 = ((4294967296 : ℕ) : ZMod 25792643401363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25792643401363 - 1) / 4703 = 5484295854 from by norm_num]
      have h2 : (3 : ZMod 25792643401363) ^ 5484295854 = ((16034357117878 : ℕ) : ZMod 25792643401363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25792643401363 - 1) / 16417 = 1571093586 from by norm_num]
      have h2 : (3 : ZMod 25792643401363) ^ 1571093586 = ((24194372565776 : ℕ) : ZMod 25792643401363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_62228321 : Nat.Prime 62228321 := by
  refine lucas_primality 62228321 (3 : ZMod 62228321) ?_ (fun q hq hd => ?_)
  · rw [show 62228321 - 1 = 62228320 from by norm_num]
    reduce_mod_char
  · have e : 62228321 - 1 = [2 ^ 5, 5 ^ 1, 7 ^ 1, 11 ^ 1, 5051 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62228321 - 1) / 2 = 31114160 from by norm_num]
      have h2 : (3 : ZMod 62228321) ^ 31114160 = ((62228320 : ℕ) : ZMod 62228321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62228321 - 1) / 5 = 12445664 from by norm_num]
      have h2 : (3 : ZMod 62228321) ^ 12445664 = ((43403201 : ℕ) : ZMod 62228321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62228321 - 1) / 7 = 8889760 from by norm_num]
      have h2 : (3 : ZMod 62228321) ^ 8889760 = ((1097205 : ℕ) : ZMod 62228321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62228321 - 1) / 11 = 5657120 from by norm_num]
      have h2 : (3 : ZMod 62228321) ^ 5657120 = ((12767969 : ℕ) : ZMod 62228321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62228321 - 1) / 5051 = 12320 from by norm_num]
      have h2 : (3 : ZMod 62228321) ^ 12320 = ((7344610 : ℕ) : ZMod 62228321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5203536083 : Nat.Prime 5203536083 := by
  refine lucas_primality 5203536083 (5 : ZMod 5203536083) ?_ (fun q hq hd => ?_)
  · rw [show 5203536083 - 1 = 5203536082 from by norm_num]
    reduce_mod_char
  · have e : 5203536083 - 1 = [2 ^ 1, 281 ^ 1, 9258961 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5203536083 - 1) / 2 = 2601768041 from by norm_num]
      have h2 : (5 : ZMod 5203536083) ^ 2601768041 = ((5203536082 : ℕ) : ZMod 5203536083) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5203536083 - 1) / 281 = 18517922 from by norm_num]
      have h2 : (5 : ZMod 5203536083) ^ 18517922 = ((624792695 : ℕ) : ZMod 5203536083) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5203536083 - 1) / 9258961 = 562 from by norm_num]
      have h2 : (5 : ZMod 5203536083) ^ 562 = ((153330139 : ℕ) : ZMod 5203536083) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_144542669 : Nat.Prime 144542669 := by
  refine lucas_primality 144542669 (2 : ZMod 144542669) ?_ (fun q hq hd => ?_)
  · rw [show 144542669 - 1 = 144542668 from by norm_num]
    reduce_mod_char
  · have e : 144542669 - 1 = [2 ^ 2, 383 ^ 1, 94349 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (144542669 - 1) / 2 = 72271334 from by norm_num]
      have h2 : (2 : ZMod 144542669) ^ 72271334 = ((144542668 : ℕ) : ZMod 144542669) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (144542669 - 1) / 383 = 377396 from by norm_num]
      have h2 : (2 : ZMod 144542669) ^ 377396 = ((126585098 : ℕ) : ZMod 144542669) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (144542669 - 1) / 94349 = 1532 from by norm_num]
      have h2 : (2 : ZMod 144542669) ^ 1532 = ((85830596 : ℕ) : ZMod 144542669) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1249678499 : Nat.Prime 1249678499 := by
  refine lucas_primality 1249678499 (6 : ZMod 1249678499) ?_ (fun q hq hd => ?_)
  · rw [show 1249678499 - 1 = 1249678498 from by norm_num]
    reduce_mod_char
  · have e : 1249678499 - 1 = [2 ^ 1, 29 ^ 1, 307 ^ 1, 70183 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1249678499 - 1) / 2 = 624839249 from by norm_num]
      have h2 : (6 : ZMod 1249678499) ^ 624839249 = ((1249678498 : ℕ) : ZMod 1249678499) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1249678499 - 1) / 29 = 43092362 from by norm_num]
      have h2 : (6 : ZMod 1249678499) ^ 43092362 = ((648079883 : ℕ) : ZMod 1249678499) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1249678499 - 1) / 307 = 4070614 from by norm_num]
      have h2 : (6 : ZMod 1249678499) ^ 4070614 = ((266073297 : ℕ) : ZMod 1249678499) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1249678499 - 1) / 70183 = 17806 from by norm_num]
      have h2 : (6 : ZMod 1249678499) ^ 17806 = ((121319156 : ℕ) : ZMod 1249678499) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_326330579 : Nat.Prime 326330579 := by
  refine lucas_primality 326330579 (7 : ZMod 326330579) ?_ (fun q hq hd => ?_)
  · rw [show 326330579 - 1 = 326330578 from by norm_num]
    reduce_mod_char
  · have e : 326330579 - 1 = [2 ^ 1, 7 ^ 1, 23 ^ 2, 139 ^ 1, 317 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326330579 - 1) / 2 = 163165289 from by norm_num]
      have h2 : (7 : ZMod 326330579) ^ 163165289 = ((326330578 : ℕ) : ZMod 326330579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326330579 - 1) / 7 = 46618654 from by norm_num]
      have h2 : (7 : ZMod 326330579) ^ 46618654 = ((20452803 : ℕ) : ZMod 326330579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326330579 - 1) / 23 = 14188286 from by norm_num]
      have h2 : (7 : ZMod 326330579) ^ 14188286 = ((96455745 : ℕ) : ZMod 326330579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326330579 - 1) / 139 = 2347702 from by norm_num]
      have h2 : (7 : ZMod 326330579) ^ 2347702 = ((253936550 : ℕ) : ZMod 326330579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326330579 - 1) / 317 = 1029434 from by norm_num]
      have h2 : (7 : ZMod 326330579) ^ 1029434 = ((324233427 : ℕ) : ZMod 326330579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2983001129 : Nat.Prime 2983001129 := by
  refine lucas_primality 2983001129 (3 : ZMod 2983001129) ?_ (fun q hq hd => ?_)
  · rw [show 2983001129 - 1 = 2983001128 from by norm_num]
    reduce_mod_char
  · have e : 2983001129 - 1 = [2 ^ 3, 103 ^ 1, 331 ^ 1, 10937 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2983001129 - 1) / 2 = 1491500564 from by norm_num]
      have h2 : (3 : ZMod 2983001129) ^ 1491500564 = ((2983001128 : ℕ) : ZMod 2983001129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2983001129 - 1) / 103 = 28961176 from by norm_num]
      have h2 : (3 : ZMod 2983001129) ^ 28961176 = ((234720012 : ℕ) : ZMod 2983001129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2983001129 - 1) / 331 = 9012088 from by norm_num]
      have h2 : (3 : ZMod 2983001129) ^ 9012088 = ((2250608017 : ℕ) : ZMod 2983001129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2983001129 - 1) / 10937 = 272744 from by norm_num]
      have h2 : (3 : ZMod 2983001129) ^ 272744 = ((2056570947 : ℕ) : ZMod 2983001129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_131282633 : Nat.Prime 131282633 := by
  refine lucas_primality 131282633 (3 : ZMod 131282633) ?_ (fun q hq hd => ?_)
  · rw [show 131282633 - 1 = 131282632 from by norm_num]
    reduce_mod_char
  · have e : 131282633 - 1 = [2 ^ 3, 13 ^ 1, 349 ^ 1, 3617 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131282633 - 1) / 2 = 65641316 from by norm_num]
      have h2 : (3 : ZMod 131282633) ^ 65641316 = ((131282632 : ℕ) : ZMod 131282633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131282633 - 1) / 13 = 10098664 from by norm_num]
      have h2 : (3 : ZMod 131282633) ^ 10098664 = ((54006941 : ℕ) : ZMod 131282633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131282633 - 1) / 349 = 376168 from by norm_num]
      have h2 : (3 : ZMod 131282633) ^ 376168 = ((55294763 : ℕ) : ZMod 131282633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131282633 - 1) / 3617 = 36296 from by norm_num]
      have h2 : (3 : ZMod 131282633) ^ 36296 = ((16105574 : ℕ) : ZMod 131282633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3536450843 : Nat.Prime 3536450843 := by
  refine lucas_primality 3536450843 (5 : ZMod 3536450843) ?_ (fun q hq hd => ?_)
  · rw [show 3536450843 - 1 = 3536450842 from by norm_num]
    reduce_mod_char
  · have e : 3536450843 - 1 = [2 ^ 1, 359 ^ 1, 4925419 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3536450843 - 1) / 2 = 1768225421 from by norm_num]
      have h2 : (5 : ZMod 3536450843) ^ 1768225421 = ((3536450842 : ℕ) : ZMod 3536450843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3536450843 - 1) / 359 = 9850838 from by norm_num]
      have h2 : (5 : ZMod 3536450843) ^ 9850838 = ((2755820094 : ℕ) : ZMod 3536450843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3536450843 - 1) / 4925419 = 718 from by norm_num]
      have h2 : (5 : ZMod 3536450843) ^ 718 = ((686407923 : ℕ) : ZMod 3536450843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15012732261073 : Nat.Prime 15012732261073 := by
  refine lucas_primality 15012732261073 (5 : ZMod 15012732261073) ?_ (fun q hq hd => ?_)
  · rw [show 15012732261073 - 1 = 15012732261072 from by norm_num]
    reduce_mod_char
  · have e : 15012732261073 - 1 = [2 ^ 4, 3 ^ 1, 7 ^ 1, 13 ^ 1, 379 ^ 1, 9068551 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15012732261073 - 1) / 2 = 7506366130536 from by norm_num]
      have h2 : (5 : ZMod 15012732261073) ^ 7506366130536 = ((15012732261072 : ℕ) : ZMod 15012732261073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15012732261073 - 1) / 3 = 5004244087024 from by norm_num]
      have h2 : (5 : ZMod 15012732261073) ^ 5004244087024 = ((13887784478104 : ℕ) : ZMod 15012732261073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15012732261073 - 1) / 7 = 2144676037296 from by norm_num]
      have h2 : (5 : ZMod 15012732261073) ^ 2144676037296 = ((9947256681909 : ℕ) : ZMod 15012732261073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15012732261073 - 1) / 13 = 1154825558544 from by norm_num]
      have h2 : (5 : ZMod 15012732261073) ^ 1154825558544 = ((4268161966146 : ℕ) : ZMod 15012732261073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15012732261073 - 1) / 379 = 39611430768 from by norm_num]
      have h2 : (5 : ZMod 15012732261073) ^ 39611430768 = ((4194304 : ℕ) : ZMod 15012732261073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15012732261073 - 1) / 9068551 = 1655472 from by norm_num]
      have h2 : (5 : ZMod 15012732261073) ^ 1655472 = ((9790516762563 : ℕ) : ZMod 15012732261073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1492616053 : Nat.Prime 1492616053 := by
  refine lucas_primality 1492616053 (2 : ZMod 1492616053) ?_ (fun q hq hd => ?_)
  · rw [show 1492616053 - 1 = 1492616052 from by norm_num]
    reduce_mod_char
  · have e : 1492616053 - 1 = [2 ^ 2, 3 ^ 3, 409 ^ 1, 33791 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1492616053 - 1) / 2 = 746308026 from by norm_num]
      have h2 : (2 : ZMod 1492616053) ^ 746308026 = ((1492616052 : ℕ) : ZMod 1492616053) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1492616053 - 1) / 3 = 497538684 from by norm_num]
      have h2 : (2 : ZMod 1492616053) ^ 497538684 = ((1262591326 : ℕ) : ZMod 1492616053) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1492616053 - 1) / 409 = 3649428 from by norm_num]
      have h2 : (2 : ZMod 1492616053) ^ 3649428 = ((855230646 : ℕ) : ZMod 1492616053) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1492616053 - 1) / 33791 = 44172 from by norm_num]
      have h2 : (2 : ZMod 1492616053) ^ 44172 = ((676933573 : ℕ) : ZMod 1492616053) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1074456464321 : Nat.Prime 1074456464321 := by
  refine lucas_primality 1074456464321 (13 : ZMod 1074456464321) ?_ (fun q hq hd => ?_)
  · rw [show 1074456464321 - 1 = 1074456464320 from by norm_num]
    reduce_mod_char
  · have e : 1074456464321 - 1 = [2 ^ 6, 5 ^ 1, 179 ^ 1, 389 ^ 1, 48221 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1074456464321 - 1) / 2 = 537228232160 from by norm_num]
      have h2 : (13 : ZMod 1074456464321) ^ 537228232160 = ((1074456464320 : ℕ) : ZMod 1074456464321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1074456464321 - 1) / 5 = 214891292864 from by norm_num]
      have h2 : (13 : ZMod 1074456464321) ^ 214891292864 = ((129507674464 : ℕ) : ZMod 1074456464321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1074456464321 - 1) / 179 = 6002550080 from by norm_num]
      have h2 : (13 : ZMod 1074456464321) ^ 6002550080 = ((59277748998 : ℕ) : ZMod 1074456464321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1074456464321 - 1) / 389 = 2762098880 from by norm_num]
      have h2 : (13 : ZMod 1074456464321) ^ 2762098880 = ((384973636596 : ℕ) : ZMod 1074456464321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1074456464321 - 1) / 48221 = 22281920 from by norm_num]
      have h2 : (13 : ZMod 1074456464321) ^ 22281920 = ((939390341753 : ℕ) : ZMod 1074456464321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_175737073 : Nat.Prime 175737073 := by
  refine lucas_primality 175737073 (5 : ZMod 175737073) ?_ (fun q hq hd => ?_)
  · rw [show 175737073 - 1 = 175737072 from by norm_num]
    reduce_mod_char
  · have e : 175737073 - 1 = [2 ^ 4, 3 ^ 1, 7 ^ 1, 563 ^ 1, 929 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175737073 - 1) / 2 = 87868536 from by norm_num]
      have h2 : (5 : ZMod 175737073) ^ 87868536 = ((175737072 : ℕ) : ZMod 175737073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175737073 - 1) / 3 = 58579024 from by norm_num]
      have h2 : (5 : ZMod 175737073) ^ 58579024 = ((73303235 : ℕ) : ZMod 175737073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175737073 - 1) / 7 = 25105296 from by norm_num]
      have h2 : (5 : ZMod 175737073) ^ 25105296 = ((1428976 : ℕ) : ZMod 175737073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175737073 - 1) / 563 = 312144 from by norm_num]
      have h2 : (5 : ZMod 175737073) ^ 312144 = ((77396068 : ℕ) : ZMod 175737073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175737073 - 1) / 929 = 189168 from by norm_num]
      have h2 : (5 : ZMod 175737073) ^ 189168 = ((51206118 : ℕ) : ZMod 175737073) := by
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

theorem prime_304612639 : Nat.Prime 304612639 := by
  refine lucas_primality 304612639 (7 : ZMod 304612639) ?_ (fun q hq hd => ?_)
  · rw [show 304612639 - 1 = 304612638 from by norm_num]
    reduce_mod_char
  · have e : 304612639 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 37 ^ 1, 124739 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (304612639 - 1) / 2 = 152306319 from by norm_num]
      have h2 : (7 : ZMod 304612639) ^ 152306319 = ((304612638 : ℕ) : ZMod 304612639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (304612639 - 1) / 3 = 101537546 from by norm_num]
      have h2 : (7 : ZMod 304612639) ^ 101537546 = ((238655598 : ℕ) : ZMod 304612639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (304612639 - 1) / 11 = 27692058 from by norm_num]
      have h2 : (7 : ZMod 304612639) ^ 27692058 = ((207065366 : ℕ) : ZMod 304612639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (304612639 - 1) / 37 = 8232774 from by norm_num]
      have h2 : (7 : ZMod 304612639) ^ 8232774 = ((217112755 : ℕ) : ZMod 304612639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (304612639 - 1) / 124739 = 2442 from by norm_num]
      have h2 : (7 : ZMod 304612639) ^ 2442 = ((241874646 : ℕ) : ZMod 304612639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1807447391779 : Nat.Prime 1807447391779 := by
  refine lucas_primality 1807447391779 (15 : ZMod 1807447391779) ?_ (fun q hq hd => ?_)
  · rw [show 1807447391779 - 1 = 1807447391778 from by norm_num]
    reduce_mod_char
  · have e : 1807447391779 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 71 ^ 1, 313 ^ 1, 431 ^ 1, 4493 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1807447391779 - 1) / 2 = 903723695889 from by norm_num]
      have h2 : (15 : ZMod 1807447391779) ^ 903723695889 = ((1807447391778 : ℕ) : ZMod 1807447391779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1807447391779 - 1) / 3 = 602482463926 from by norm_num]
      have h2 : (15 : ZMod 1807447391779) ^ 602482463926 = ((766205195307 : ℕ) : ZMod 1807447391779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1807447391779 - 1) / 7 = 258206770254 from by norm_num]
      have h2 : (15 : ZMod 1807447391779) ^ 258206770254 = ((1468309492770 : ℕ) : ZMod 1807447391779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1807447391779 - 1) / 71 = 25457005518 from by norm_num]
      have h2 : (15 : ZMod 1807447391779) ^ 25457005518 = ((1629217136525 : ℕ) : ZMod 1807447391779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1807447391779 - 1) / 313 = 5774592306 from by norm_num]
      have h2 : (15 : ZMod 1807447391779) ^ 5774592306 = ((22243939144 : ℕ) : ZMod 1807447391779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1807447391779 - 1) / 431 = 4193613438 from by norm_num]
      have h2 : (15 : ZMod 1807447391779) ^ 4193613438 = ((1242177055346 : ℕ) : ZMod 1807447391779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1807447391779 - 1) / 4493 = 402280746 from by norm_num]
      have h2 : (15 : ZMod 1807447391779) ^ 402280746 = ((1790914107984 : ℕ) : ZMod 1807447391779) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11694270587 : Nat.Prime 11694270587 := by
  refine lucas_primality 11694270587 (5 : ZMod 11694270587) ?_ (fun q hq hd => ?_)
  · rw [show 11694270587 - 1 = 11694270586 from by norm_num]
    reduce_mod_char
  · have e : 11694270587 - 1 = [2 ^ 1, 443 ^ 1, 523 ^ 1, 25237 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11694270587 - 1) / 2 = 5847135293 from by norm_num]
      have h2 : (5 : ZMod 11694270587) ^ 5847135293 = ((11694270586 : ℕ) : ZMod 11694270587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11694270587 - 1) / 443 = 26397902 from by norm_num]
      have h2 : (5 : ZMod 11694270587) ^ 26397902 = ((8709039029 : ℕ) : ZMod 11694270587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11694270587 - 1) / 523 = 22359982 from by norm_num]
      have h2 : (5 : ZMod 11694270587) ^ 22359982 = ((11155984365 : ℕ) : ZMod 11694270587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11694270587 - 1) / 25237 = 463378 from by norm_num]
      have h2 : (5 : ZMod 11694270587) ^ 463378 = ((7653971320 : ℕ) : ZMod 11694270587) := by
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

theorem prime_223439473 : Nat.Prime 223439473 := by
  refine lucas_primality 223439473 (15 : ZMod 223439473) ?_ (fun q hq hd => ?_)
  · rw [show 223439473 - 1 = 223439472 from by norm_num]
    reduce_mod_char
  · have e : 223439473 - 1 = [2 ^ 4, 3 ^ 5, 101 ^ 1, 569 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (223439473 - 1) / 2 = 111719736 from by norm_num]
      have h2 : (15 : ZMod 223439473) ^ 111719736 = ((223439472 : ℕ) : ZMod 223439473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (223439473 - 1) / 3 = 74479824 from by norm_num]
      have h2 : (15 : ZMod 223439473) ^ 74479824 = ((99700620 : ℕ) : ZMod 223439473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (223439473 - 1) / 101 = 2212272 from by norm_num]
      have h2 : (15 : ZMod 223439473) ^ 2212272 = ((57342552 : ℕ) : ZMod 223439473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (223439473 - 1) / 569 = 392688 from by norm_num]
      have h2 : (15 : ZMod 223439473) ^ 392688 = ((179983932 : ℕ) : ZMod 223439473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_111719737 : Nat.Prime 111719737 := by
  refine lucas_primality 111719737 (5 : ZMod 111719737) ?_ (fun q hq hd => ?_)
  · rw [show 111719737 - 1 = 111719736 from by norm_num]
    reduce_mod_char
  · have e : 111719737 - 1 = [2 ^ 3, 3 ^ 5, 101 ^ 1, 569 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111719737 - 1) / 2 = 55859868 from by norm_num]
      have h2 : (5 : ZMod 111719737) ^ 55859868 = ((111719736 : ℕ) : ZMod 111719737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111719737 - 1) / 3 = 37239912 from by norm_num]
      have h2 : (5 : ZMod 111719737) ^ 37239912 = ((74956532 : ℕ) : ZMod 111719737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111719737 - 1) / 101 = 1106136 from by norm_num]
      have h2 : (5 : ZMod 111719737) ^ 1106136 = ((75526959 : ℕ) : ZMod 111719737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111719737 - 1) / 569 = 196344 from by norm_num]
      have h2 : (5 : ZMod 111719737) ^ 196344 = ((109883979 : ℕ) : ZMod 111719737) := by
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

theorem prime_2796392419 : Nat.Prime 2796392419 := by
  refine lucas_primality 2796392419 (3 : ZMod 2796392419) ?_ (fun q hq hd => ?_)
  · rw [show 2796392419 - 1 = 2796392418 from by norm_num]
    reduce_mod_char
  · have e : 2796392419 - 1 = [2 ^ 1, 3 ^ 1, 191 ^ 1, 577 ^ 1, 4229 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2796392419 - 1) / 2 = 1398196209 from by norm_num]
      have h2 : (3 : ZMod 2796392419) ^ 1398196209 = ((2796392418 : ℕ) : ZMod 2796392419) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2796392419 - 1) / 3 = 932130806 from by norm_num]
      have h2 : (3 : ZMod 2796392419) ^ 932130806 = ((1806128015 : ℕ) : ZMod 2796392419) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2796392419 - 1) / 191 = 14640798 from by norm_num]
      have h2 : (3 : ZMod 2796392419) ^ 14640798 = ((2328311676 : ℕ) : ZMod 2796392419) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2796392419 - 1) / 577 = 4846434 from by norm_num]
      have h2 : (3 : ZMod 2796392419) ^ 4846434 = ((1133492655 : ℕ) : ZMod 2796392419) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2796392419 - 1) / 4229 = 661242 from by norm_num]
      have h2 : (3 : ZMod 2796392419) ^ 661242 = ((2495348895 : ℕ) : ZMod 2796392419) := by
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

theorem prime_202769117249 : Nat.Prime 202769117249 := by
  refine lucas_primality 202769117249 (3 : ZMod 202769117249) ?_ (fun q hq hd => ?_)
  · rw [show 202769117249 - 1 = 202769117248 from by norm_num]
    reduce_mod_char
  · have e : 202769117249 - 1 = [2 ^ 6, 23 ^ 1, 607 ^ 1, 226937 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (202769117249 - 1) / 2 = 101384558624 from by norm_num]
      have h2 : (3 : ZMod 202769117249) ^ 101384558624 = ((202769117248 : ℕ) : ZMod 202769117249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (202769117249 - 1) / 23 = 8816048576 from by norm_num]
      have h2 : (3 : ZMod 202769117249) ^ 8816048576 = ((129374216856 : ℕ) : ZMod 202769117249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (202769117249 - 1) / 607 = 334051264 from by norm_num]
      have h2 : (3 : ZMod 202769117249) ^ 334051264 = ((29687349808 : ℕ) : ZMod 202769117249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (202769117249 - 1) / 226937 = 893504 from by norm_num]
      have h2 : (3 : ZMod 202769117249) ^ 893504 = ((174687516971 : ℕ) : ZMod 202769117249) := by
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

theorem prime_85596630163086389 : Nat.Prime 85596630163086389 := by
  refine lucas_primality 85596630163086389 (2 : ZMod 85596630163086389) ?_ (fun q hq hd => ?_)
  · rw [show 85596630163086389 - 1 = 85596630163086388 from by norm_num]
    reduce_mod_char
  · have e : 85596630163086389 - 1 = [2 ^ 2, 8293 ^ 1, 427877 ^ 1, 6030677 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85596630163086389 - 1) / 2 = 42798315081543194 from by norm_num]
      have h2 : (2 : ZMod 85596630163086389) ^ 42798315081543194 = ((85596630163086388 : ℕ) : ZMod 85596630163086389) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85596630163086389 - 1) / 8293 = 10321551930916 from by norm_num]
      have h2 : (2 : ZMod 85596630163086389) ^ 10321551930916 = ((58654273452377644 : ℕ) : ZMod 85596630163086389) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85596630163086389 - 1) / 427877 = 200049617444 from by norm_num]
      have h2 : (2 : ZMod 85596630163086389) ^ 200049617444 = ((58848217304965270 : ℕ) : ZMod 85596630163086389) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85596630163086389 - 1) / 6030677 = 14193535844 from by norm_num]
      have h2 : (2 : ZMod 85596630163086389) ^ 14193535844 = ((32339648254081918 : ℕ) : ZMod 85596630163086389) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2203942033439148343973 : Nat.Prime 2203942033439148343973 := by
  refine lucas_primality 2203942033439148343973 (3 : ZMod 2203942033439148343973) ?_ (fun q hq hd => ?_)
  · rw [show 2203942033439148343973 - 1 = 2203942033439148343972 from by norm_num]
    reduce_mod_char
  · have e : 2203942033439148343973 - 1 = [2 ^ 2, 41 ^ 1, 157 ^ 1, 85596630163086389 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2203942033439148343973 - 1) / 2 = 1101971016719574171986 from by norm_num]
      have h2 : (3 : ZMod 2203942033439148343973) ^ 1101971016719574171986 = ((2203942033439148343972 : ℕ) : ZMod 2203942033439148343973) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2203942033439148343973 - 1) / 41 = 53754683742418252292 from by norm_num]
      have h2 : (3 : ZMod 2203942033439148343973) ^ 53754683742418252292 = ((1228846018638548144220 : ℕ) : ZMod 2203942033439148343973) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2203942033439148343973 - 1) / 157 = 14037847346746167796 from by norm_num]
      have h2 : (3 : ZMod 2203942033439148343973) ^ 14037847346746167796 = ((295147905179352825856 : ℕ) : ZMod 2203942033439148343973) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_85596630163086389).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2203942033439148343973 - 1) / 85596630163086389 = 25748 from by norm_num]
      have h2 : (3 : ZMod 2203942033439148343973) ^ 25748 = ((1689297897053767320805 : ℕ) : ZMod 2203942033439148343973) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_12239719573537 : Nat.Prime 12239719573537 := by
  refine lucas_primality 12239719573537 (5 : ZMod 12239719573537) ?_ (fun q hq hd => ?_)
  · rw [show 12239719573537 - 1 = 12239719573536 from by norm_num]
    reduce_mod_char
  · have e : 12239719573537 - 1 = [2 ^ 5, 3 ^ 6, 7 ^ 1, 13 ^ 1, 41 ^ 1, 140627 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12239719573537 - 1) / 2 = 6119859786768 from by norm_num]
      have h2 : (5 : ZMod 12239719573537) ^ 6119859786768 = ((12239719573536 : ℕ) : ZMod 12239719573537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12239719573537 - 1) / 3 = 4079906524512 from by norm_num]
      have h2 : (5 : ZMod 12239719573537) ^ 4079906524512 = ((9858806733279 : ℕ) : ZMod 12239719573537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12239719573537 - 1) / 7 = 1748531367648 from by norm_num]
      have h2 : (5 : ZMod 12239719573537) ^ 1748531367648 = ((5872900686124 : ℕ) : ZMod 12239719573537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12239719573537 - 1) / 13 = 941516890272 from by norm_num]
      have h2 : (5 : ZMod 12239719573537) ^ 941516890272 = ((8823581046230 : ℕ) : ZMod 12239719573537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12239719573537 - 1) / 41 = 298529745696 from by norm_num]
      have h2 : (5 : ZMod 12239719573537) ^ 298529745696 = ((6812326238690 : ℕ) : ZMod 12239719573537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12239719573537 - 1) / 140627 = 87036768 from by norm_num]
      have h2 : (5 : ZMod 12239719573537) ^ 87036768 = ((4440558378602 : ℕ) : ZMod 12239719573537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_260541521 : Nat.Prime 260541521 := by
  refine lucas_primality 260541521 (3 : ZMod 260541521) ?_ (fun q hq hd => ?_)
  · rw [show 260541521 - 1 = 260541520 from by norm_num]
    reduce_mod_char
  · have e : 260541521 - 1 = [2 ^ 4, 5 ^ 1, 227 ^ 1, 14347 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260541521 - 1) / 2 = 130270760 from by norm_num]
      have h2 : (3 : ZMod 260541521) ^ 130270760 = ((260541520 : ℕ) : ZMod 260541521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260541521 - 1) / 5 = 52108304 from by norm_num]
      have h2 : (3 : ZMod 260541521) ^ 52108304 = ((201440543 : ℕ) : ZMod 260541521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260541521 - 1) / 227 = 1147760 from by norm_num]
      have h2 : (3 : ZMod 260541521) ^ 1147760 = ((223883239 : ℕ) : ZMod 260541521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (260541521 - 1) / 14347 = 18160 from by norm_num]
      have h2 : (3 : ZMod 260541521) ^ 18160 = ((32237697 : ℕ) : ZMod 260541521) := by
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

theorem prime_7152893721041 : Nat.Prime 7152893721041 := by
  refine lucas_primality 7152893721041 (3 : ZMod 7152893721041) ?_ (fun q hq hd => ?_)
  · rw [show 7152893721041 - 1 = 7152893721040 from by norm_num]
    reduce_mod_char
  · have e : 7152893721041 - 1 = [2 ^ 4, 5 ^ 1, 37 ^ 1, 173 ^ 1, 181 ^ 1, 229 ^ 1, 337 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7152893721041 - 1) / 2 = 3576446860520 from by norm_num]
      have h2 : (3 : ZMod 7152893721041) ^ 3576446860520 = ((7152893721040 : ℕ) : ZMod 7152893721041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7152893721041 - 1) / 5 = 1430578744208 from by norm_num]
      have h2 : (3 : ZMod 7152893721041) ^ 1430578744208 = ((6249291118053 : ℕ) : ZMod 7152893721041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7152893721041 - 1) / 37 = 193321451920 from by norm_num]
      have h2 : (3 : ZMod 7152893721041) ^ 193321451920 = ((1721308329875 : ℕ) : ZMod 7152893721041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7152893721041 - 1) / 173 = 41346206480 from by norm_num]
      have h2 : (3 : ZMod 7152893721041) ^ 41346206480 = ((6878015814097 : ℕ) : ZMod 7152893721041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7152893721041 - 1) / 181 = 39518749840 from by norm_num]
      have h2 : (3 : ZMod 7152893721041) ^ 39518749840 = ((1716996544902 : ℕ) : ZMod 7152893721041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7152893721041 - 1) / 229 = 31235343760 from by norm_num]
      have h2 : (3 : ZMod 7152893721041) ^ 31235343760 = ((6971397445781 : ℕ) : ZMod 7152893721041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7152893721041 - 1) / 337 = 21225203920 from by norm_num]
      have h2 : (3 : ZMod 7152893721041) ^ 21225203920 = ((4612468935529 : ℕ) : ZMod 7152893721041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6012271351 : Nat.Prime 6012271351 := by
  refine lucas_primality 6012271351 (6 : ZMod 6012271351) ?_ (fun q hq hd => ?_)
  · rw [show 6012271351 - 1 = 6012271350 from by norm_num]
    reduce_mod_char
  · have e : 6012271351 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 2, 13360603 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6012271351 - 1) / 2 = 3006135675 from by norm_num]
      have h2 : (6 : ZMod 6012271351) ^ 3006135675 = ((6012271350 : ℕ) : ZMod 6012271351) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6012271351 - 1) / 3 = 2004090450 from by norm_num]
      have h2 : (6 : ZMod 6012271351) ^ 2004090450 = ((5259204231 : ℕ) : ZMod 6012271351) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6012271351 - 1) / 5 = 1202454270 from by norm_num]
      have h2 : (6 : ZMod 6012271351) ^ 1202454270 = ((3098197564 : ℕ) : ZMod 6012271351) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6012271351 - 1) / 13360603 = 450 from by norm_num]
      have h2 : (6 : ZMod 6012271351) ^ 450 = ((124237653 : ℕ) : ZMod 6012271351) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3830538323149121 : Nat.Prime 3830538323149121 := by
  refine lucas_primality 3830538323149121 (7 : ZMod 3830538323149121) ?_ (fun q hq hd => ?_)
  · rw [show 3830538323149121 - 1 = 3830538323149120 from by norm_num]
    reduce_mod_char
  · have e : 3830538323149121 - 1 = [2 ^ 6, 5 ^ 1, 11 ^ 1, 181 ^ 1, 6012271351 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3830538323149121 - 1) / 2 = 1915269161574560 from by norm_num]
      have h2 : (7 : ZMod 3830538323149121) ^ 1915269161574560 = ((3830538323149120 : ℕ) : ZMod 3830538323149121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3830538323149121 - 1) / 5 = 766107664629824 from by norm_num]
      have h2 : (7 : ZMod 3830538323149121) ^ 766107664629824 = ((3736864549674958 : ℕ) : ZMod 3830538323149121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3830538323149121 - 1) / 11 = 348230756649920 from by norm_num]
      have h2 : (7 : ZMod 3830538323149121) ^ 348230756649920 = ((1724867299164807 : ℕ) : ZMod 3830538323149121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3830538323149121 - 1) / 181 = 21163195155520 from by norm_num]
      have h2 : (7 : ZMod 3830538323149121) ^ 21163195155520 = ((2903551014878548 : ℕ) : ZMod 3830538323149121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6012271351).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3830538323149121 - 1) / 6012271351 = 637120 from by norm_num]
      have h2 : (7 : ZMod 3830538323149121) ^ 637120 = ((3691567782424277 : ℕ) : ZMod 3830538323149121) := by
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

theorem prime_14254355329 : Nat.Prime 14254355329 := by
  refine lucas_primality 14254355329 (13 : ZMod 14254355329) ?_ (fun q hq hd => ?_)
  · rw [show 14254355329 - 1 = 14254355328 from by norm_num]
    reduce_mod_char
  · have e : 14254355329 - 1 = [2 ^ 7, 3 ^ 1, 71 ^ 1, 522827 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14254355329 - 1) / 2 = 7127177664 from by norm_num]
      have h2 : (13 : ZMod 14254355329) ^ 7127177664 = ((14254355328 : ℕ) : ZMod 14254355329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14254355329 - 1) / 3 = 4751451776 from by norm_num]
      have h2 : (13 : ZMod 14254355329) ^ 4751451776 = ((6219795169 : ℕ) : ZMod 14254355329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14254355329 - 1) / 71 = 200765568 from by norm_num]
      have h2 : (13 : ZMod 14254355329) ^ 200765568 = ((12313507476 : ℕ) : ZMod 14254355329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14254355329 - 1) / 522827 = 27264 from by norm_num]
      have h2 : (13 : ZMod 14254355329) ^ 27264 = ((835828774 : ℕ) : ZMod 14254355329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_286297736737 : Nat.Prime 286297736737 := by
  refine lucas_primality 286297736737 (7 : ZMod 286297736737) ?_ (fun q hq hd => ?_)
  · rw [show 286297736737 - 1 = 286297736736 from by norm_num]
    reduce_mod_char
  · have e : 286297736737 - 1 = [2 ^ 5, 3 ^ 1, 11 ^ 1, 79 ^ 2, 43441 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (286297736737 - 1) / 2 = 143148868368 from by norm_num]
      have h2 : (7 : ZMod 286297736737) ^ 143148868368 = ((286297736736 : ℕ) : ZMod 286297736737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (286297736737 - 1) / 3 = 95432578912 from by norm_num]
      have h2 : (7 : ZMod 286297736737) ^ 95432578912 = ((178026525535 : ℕ) : ZMod 286297736737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (286297736737 - 1) / 11 = 26027066976 from by norm_num]
      have h2 : (7 : ZMod 286297736737) ^ 26027066976 = ((122434056610 : ℕ) : ZMod 286297736737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (286297736737 - 1) / 79 = 3624021984 from by norm_num]
      have h2 : (7 : ZMod 286297736737) ^ 3624021984 = ((217095428881 : ℕ) : ZMod 286297736737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (286297736737 - 1) / 43441 = 6590496 from by norm_num]
      have h2 : (7 : ZMod 286297736737) ^ 6590496 = ((180568610765 : ℕ) : ZMod 286297736737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11011451413 : Nat.Prime 11011451413 := by
  refine lucas_primality 11011451413 (11 : ZMod 11011451413) ?_ (fun q hq hd => ?_)
  · rw [show 11011451413 - 1 = 11011451412 from by norm_num]
    reduce_mod_char
  · have e : 11011451413 - 1 = [2 ^ 2, 3 ^ 1, 13 ^ 1, 17 ^ 2, 244243 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11011451413 - 1) / 2 = 5505725706 from by norm_num]
      have h2 : (11 : ZMod 11011451413) ^ 5505725706 = ((11011451412 : ℕ) : ZMod 11011451413) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11011451413 - 1) / 3 = 3670483804 from by norm_num]
      have h2 : (11 : ZMod 11011451413) ^ 3670483804 = ((4496608492 : ℕ) : ZMod 11011451413) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11011451413 - 1) / 13 = 847034724 from by norm_num]
      have h2 : (11 : ZMod 11011451413) ^ 847034724 = ((7403186821 : ℕ) : ZMod 11011451413) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11011451413 - 1) / 17 = 647732436 from by norm_num]
      have h2 : (11 : ZMod 11011451413) ^ 647732436 = ((5212062716 : ℕ) : ZMod 11011451413) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11011451413 - 1) / 244243 = 45084 from by norm_num]
      have h2 : (11 : ZMod 11011451413) ^ 45084 = ((9754320447 : ℕ) : ZMod 11011451413) := by
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

set_option maxHeartbeats 22000000 in
theorem odd_0 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d ∈ ({263, 277, 281, 283, 293, 307, 317, 331, 337, 349, 359, 367, 379, 389, 397, 401, 431, 433, 439,
      443, 449, 461, 467, 479, 499, 521, 523, 541, 547, 557, 569, 571, 577, 587, 599, 607, 631,
      641, 647, 659, 661, 677, 683, 709, 727, 743, 751, 787, 797, 807} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 263) h  -- d = 263: 5 | 1579+1, 79+1
    rw [show (2:ℕ) ^ 263 = (2 ^ 200) ^ 1 * 2 ^ 63 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 63 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1579 : 1579 ∈ P := S2 1579 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1579 (by norm_num))
    have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 1579 g1579 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1579 g1579 79 g79 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 277) h  -- d = 277: 7 | 25792643401363+1, 13+1
    rw [show (2:ℕ) ^ 277 = (2 ^ 200) ^ 1 * 2 ^ 77 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 77 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g25792643401363 : 25792643401363 ∈ P := S2 25792643401363 prime_25792643401363 (by norm_num) (hnz (by norm_num)) (R 25792643401363 (by norm_num))
    have g62228321 : 62228321 ∈ P := S1 62228321 prime_62228321 (by norm_num) (hnz (by norm_num)) 25792643401363 g25792643401363 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 62228321 g62228321 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 25792643401363 g25792643401363 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 281) h  -- d = 281: 29^2 | 144542669+1
    rw [show (2:ℕ) ^ 281 = (2 ^ 200) ^ 1 * 2 ^ 81 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 81 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5203536083 : 5203536083 ∈ P := S2 5203536083 prime_5203536083 (by norm_num) (hnz (by norm_num)) (R 5203536083 (by norm_num))
    have g144542669 : 144542669 ∈ P := S1 144542669 prime_144542669 (by norm_num) (hnz (by norm_num)) 5203536083 g5203536083 (by norm_num)
    exact S6 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 144542669 g144542669 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 283) h  -- d = 283: 5^2 | 1699+1
    rw [show (2:ℕ) ^ 283 = (2 ^ 200) ^ 1 * 2 ^ 83 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 83 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1699 : 1699 ∈ P := S2 1699 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1699 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1699 g1699 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 293) h  -- d = 293: 7^2 | 587+1
    rw [show (2:ℕ) ^ 293 = (2 ^ 200) ^ 1 * 2 ^ 93 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 93 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g587 : 587 ∈ P := S2 587 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 587 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 587 g587 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 307) h  -- d = 307: 5^2 | 1249678499+1
    rw [show (2:ℕ) ^ 307 = (2 ^ 200) ^ 1 * 2 ^ 107 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 107 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1249678499 : 1249678499 ∈ P := S2 1249678499 prime_1249678499 (by norm_num) (hnz (by norm_num)) (R 1249678499 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1249678499 g1249678499 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 317) h  -- d = 317: 13^2 | 337+1
    rw [show (2:ℕ) ^ 317 = (2 ^ 200) ^ 1 * 2 ^ 117 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 117 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g326330579 : 326330579 ∈ P := S2 326330579 prime_326330579 (by norm_num) (hnz (by norm_num)) (R 326330579 (by norm_num))
    have g337 : 337 ∈ P := S1 337 (by norm_num) (by norm_num) (hnz (by norm_num)) 326330579 g326330579 (by norm_num)
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 337 g337 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 331) h  -- d = 331: 5 | 2983001129+1, 29+1
    rw [show (2:ℕ) ^ 331 = (2 ^ 200) ^ 1 * 2 ^ 131 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 131 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2983001129 : 2983001129 ∈ P := S2 2983001129 prime_2983001129 (by norm_num) (hnz (by norm_num)) (R 2983001129 (by norm_num))
    have g521 : 521 ∈ P := S1 521 (by norm_num) (by norm_num) (hnz (by norm_num)) 2983001129 g2983001129 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 521 g521 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2983001129 g2983001129 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 337) h  -- d = 337: 5 | 21569+1, 719+1
    rw [show (2:ℕ) ^ 337 = (2 ^ 200) ^ 1 * 2 ^ 137 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 137 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g21569 : 21569 ∈ P := S2 21569 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 21569 (by norm_num))
    have g719 : 719 ∈ P := S1 719 (by norm_num) (by norm_num) (hnz (by norm_num)) 21569 g21569 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 21569 g21569 719 g719 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 349) h  -- d = 349: 7^2 | 130241+1
    rw [show (2:ℕ) ^ 349 = (2 ^ 200) ^ 1 * 2 ^ 149 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 149 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g131282633 : 131282633 ∈ P := S2 131282633 prime_131282633 (by norm_num) (hnz (by norm_num)) (R 131282633 (by norm_num))
    have g3125777 : 3125777 ∈ P := S1 3125777 (by norm_num) (by norm_num) (hnz (by norm_num)) 131282633 g131282633 (by norm_num)
    have g520963 : 520963 ∈ P := S1 520963 (by norm_num) (by norm_num) (hnz (by norm_num)) 3125777 g3125777 (by norm_num)
    have g130241 : 130241 ∈ P := S1 130241 (by norm_num) (by norm_num) (hnz (by norm_num)) 520963 g520963 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 130241 g130241 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 359) h  -- d = 359: 61 | 3^5+1, 3536450843+1
    rw [show (2:ℕ) ^ 359 = (2 ^ 200) ^ 1 * 2 ^ 159 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 159 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3536450843 : 3536450843 ∈ P := S2 3536450843 prime_3536450843 (by norm_num) (hnz (by norm_num)) (R 3536450843 (by norm_num))
    exact S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 3536450843 g3536450843 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 367) h  -- d = 367: 5 | 19819+1, 19+1
    rw [show (2:ℕ) ^ 367 = (2 ^ 200) ^ 1 * 2 ^ 167 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 167 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g19819 : 19819 ∈ P := S2 19819 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 19819 (by norm_num))
    have g2203 : 2203 ∈ P := S2 2203 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2203 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 2203 g2203 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19819 g19819 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 379) h  -- d = 379: 5 | 7245709+1, 19+1
    rw [show (2:ℕ) ^ 379 = (2 ^ 200) ^ 1 * 2 ^ 179 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 179 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g15012732261073 : 15012732261073 ∈ P := S2 15012732261073 prime_15012732261073 (by norm_num) (hnz (by norm_num)) (R 15012732261073 (by norm_num))
    have g1492616053 : 1492616053 ∈ P := S1 1492616053 prime_1492616053 (by norm_num) (hnz (by norm_num)) 15012732261073 g15012732261073 (by norm_num)
    have g7245709 : 7245709 ∈ P := S1 7245709 (by norm_num) (by norm_num) (hnz (by norm_num)) 1492616053 g1492616053 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 7245709 g7245709 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 7245709 g7245709 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 389) h  -- d = 389: 17 | 1019+1, 1597+1
    rw [show (2:ℕ) ^ 389 = (2 ^ 200) ^ 1 * 2 ^ 189 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 189 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1074456464321 : 1074456464321 ∈ P := S2 1074456464321 prime_1074456464321 (by norm_num) (hnz (by norm_num)) (R 1074456464321 (by norm_num))
    have g1019 : 1019 ∈ P := S1 1019 (by norm_num) (by norm_num) (hnz (by norm_num)) 1074456464321 g1074456464321 (by norm_num)
    have g175737073 : 175737073 ∈ P := S1 175737073 prime_175737073 (by norm_num) (hnz (by norm_num)) 1074456464321 g1074456464321 (by norm_num)
    have g1597 : 1597 ∈ P := S1 1597 (by norm_num) (by norm_num) (hnz (by norm_num)) 175737073 g175737073 (by norm_num)
    exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 1019 g1019 1597 g1597 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 397) h  -- d = 397: 5^2 | 13499+1
    rw [show (2:ℕ) ^ 397 = (2 ^ 200) ^ 1 * 2 ^ 197 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 197 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13499 : 13499 ∈ P := S2 13499 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13499 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 13499 g13499 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 401) h  -- d = 401: 5 | 304612639+1, 19+1
    rw [show (2:ℕ) ^ 401 = (2 ^ 200) ^ 2 * 2 ^ 1 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 1 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g18885983617 : 18885983617 ∈ P := S2 18885983617 prime_18885983617 (by norm_num) (hnz (by norm_num)) (R 18885983617 (by norm_num))
    have g304612639 : 304612639 ∈ P := S1 304612639 prime_304612639 (by norm_num) (hnz (by norm_num)) 18885983617 g18885983617 (by norm_num)
    have g40507 : 40507 ∈ P := S1 40507 (by norm_num) (by norm_num) (hnz (by norm_num)) 304612639 g304612639 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 40507 g40507 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 304612639 g304612639 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 431) h  -- d = 431: 5 | 1807447391779+1, 19+1
    rw [show (2:ℕ) ^ 431 = (2 ^ 200) ^ 2 * 2 ^ 31 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 31 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1807447391779 : 1807447391779 ∈ P := S2 1807447391779 prime_1807447391779 (by norm_num) (hnz (by norm_num)) (R 1807447391779 (by norm_num))
    have g7618003 : 7618003 ∈ P := S1 7618003 (by norm_num) (by norm_num) (hnz (by norm_num)) 1807447391779 g1807447391779 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 7618003 g7618003 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1807447391779 g1807447391779 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 433) h  -- d = 433: 5 | 19979+1, 19+1
    rw [show (2:ℕ) ^ 433 = (2 ^ 200) ^ 2 * 2 ^ 33 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 33 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2837017 : 2837017 ∈ P := S2 2837017 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2837017 (by norm_num))
    have g19979 : 19979 ∈ P := S1 19979 (by norm_num) (by norm_num) (hnz (by norm_num)) 2837017 g2837017 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 19979 g19979 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19979 g19979 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 439) h  -- d = 439: 7 | 3740281+1, 13+1
    rw [show (2:ℕ) ^ 439 = (2 ^ 200) ^ 2 * 2 ^ 39 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 39 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3740281 : 3740281 ∈ P := S2 3740281 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3740281 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 3740281 g3740281 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 3740281 g3740281 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 443) h  -- d = 443: 31 | 48731+1, 61+1
    rw [show (2:ℕ) ^ 443 = (2 ^ 200) ^ 2 * 2 ^ 43 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 43 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g48731 : 48731 ∈ P := S2 48731 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 48731 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 48731 g48731 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 449) h  -- d = 449: 3^7 | (2^449+1) prod (p+1), p in {194867, 4332851}
    rw [show (2:ℕ) ^ 449 = (2 ^ 200) ^ 2 * 2 ^ 49 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 49 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g194867 : 194867 ∈ P := S2 194867 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 194867 (by norm_num))
    have g4332851 : 4332851 ∈ P := S2 4332851 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4332851 (by norm_num))
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g194867 (by simp) (by norm_num : 3 ^ 2 ∣ 194867 + 1)
    have b2 := bud_cons b1 g4332851 (by simp) (by norm_num : 3 ^ 4 ∣ 4332851 + 1)
    exact budget_kernel3 hP h3P E b2.1 ((pow_dvd_pow 3 (by norm_num)).trans b2.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 461) h  -- d = 461: 7^2 | 110641+1
    rw [show (2:ℕ) ^ 461 = (2 ^ 200) ^ 2 * 2 ^ 61 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 61 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g110641 : 110641 ∈ P := S2 110641 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 110641 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 110641 g110641 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 467) h  -- d = 467: 11 | 16851229+1, 307+1
    rw [show (2:ℕ) ^ 467 = (2 ^ 200) ^ 2 * 2 ^ 67 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 67 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g33702457 : 33702457 ∈ P := S2 33702457 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 33702457 (by norm_num))
    have g16851229 : 16851229 ∈ P := S1 16851229 (by norm_num) (by norm_num) (hnz (by norm_num)) 33702457 g33702457 (by norm_num)
    have g307 : 307 ∈ P := S1 307 (by norm_num) (by norm_num) (hnz (by norm_num)) 16851229 g16851229 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 16851229 g16851229 307 g307 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 479) h  -- d = 479: 71 | 3833+1, 2129+1
    rw [show (2:ℕ) ^ 479 = (2 ^ 200) ^ 2 * 2 ^ 79 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 79 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3833 : 3833 ∈ P := S2 3833 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3833 (by norm_num))
    have g38321 : 38321 ∈ P := S2 38321 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 38321 (by norm_num))
    have g2129 : 2129 ∈ P := S1 2129 (by norm_num) (by norm_num) (hnz (by norm_num)) 38321 g38321 (by norm_num)
    exact absurd (S3 71 (by norm_num) (by norm_num) (hnz (by norm_num)) 3833 g3833 2129 g2129 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 499) h  -- d = 499: 7 | 163673+1, 433+1
    rw [show (2:ℕ) ^ 499 = (2 ^ 200) ^ 2 * 2 ^ 99 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 99 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g163673 : 163673 ∈ P := S2 163673 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 163673 (by norm_num))
    have g433 : 433 ∈ P := S1 433 (by norm_num) (by norm_num) (hnz (by norm_num)) 163673 g163673 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 163673 g163673 433 g433 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 521) h  -- d = 521: 3^8 | (2^521+1) prod (p+1), p in {501203, 11, 3797, 53}
    rw [show (2:ℕ) ^ 521 = (2 ^ 200) ^ 2 * 2 ^ 121 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 121 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g501203 : 501203 ∈ P := S2 501203 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 501203 (by norm_num))
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 501203 g501203 (by norm_num)
    have g3797 : 3797 ∈ P := S1 3797 (by norm_num) (by norm_num) (hnz (by norm_num)) 501203 g501203 (by norm_num)
    have g211 : 211 ∈ P := S1 211 (by norm_num) (by norm_num) (hnz (by norm_num)) 3797 g3797 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 211 g211 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g501203 (by simp) (by norm_num : 3 ^ 1 ∣ 501203 + 1)
    have b2 := bud_cons b1 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b3 := bud_cons b2 g3797 (by simp) (by norm_num : 3 ^ 2 ∣ 3797 + 1)
    have b4 := bud_cons b3 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 523) h  -- d = 523: 11 | 36667531+1, 11694270587+1
    rw [show (2:ℕ) ^ 523 = (2 ^ 200) ^ 2 * 2 ^ 123 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 123 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g36667531 : 36667531 ∈ P := S2 36667531 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 36667531 (by norm_num))
    have g11694270587 : 11694270587 ∈ P := S2 11694270587 prime_11694270587 (by norm_num) (hnz (by norm_num)) (R 11694270587 (by norm_num))
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 36667531 g36667531 11694270587 g11694270587 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 541) h  -- d = 541: 3^6 | (2^541+1) prod (p+1), p in {86561, 5, 23}
    rw [show (2:ℕ) ^ 541 = (2 ^ 200) ^ 2 * 2 ^ 141 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 141 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g86561 : 86561 ∈ P := S2 86561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 86561 (by norm_num))
    have g229 : 229 ∈ P := S1 229 (by norm_num) (by norm_num) (hnz (by norm_num)) 86561 g86561 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 229 g229 (by norm_num)
    have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 229 g229 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g86561 (by simp) (by norm_num : 3 ^ 3 ∣ 86561 + 1)
    have b2 := bud_cons b1 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b3 := bud_cons b2 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 547) h  -- d = 547: 5^2 | 1533926272849+1
    rw [show (2:ℕ) ^ 547 = (2 ^ 200) ^ 2 * 2 ^ 147 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 147 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1533926272849 : 1533926272849 ∈ P := S2 1533926272849 prime_1533926272849 (by norm_num) (hnz (by norm_num)) (R 1533926272849 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1533926272849 g1533926272849 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 557) h  -- d = 557: 5 | 124769+1, 4159+1
    rw [show (2:ℕ) ^ 557 = (2 ^ 200) ^ 2 * 2 ^ 157 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 157 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g124769 : 124769 ∈ P := S2 124769 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 124769 (by norm_num))
    have g4159 : 4159 ∈ P := S1 4159 (by norm_num) (by norm_num) (hnz (by norm_num)) 124769 g124769 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 124769 g124769 4159 g4159 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 569) h  -- d = 569: 13 | 10243+1, 111719737+1
    rw [show (2:ℕ) ^ 569 = (2 ^ 200) ^ 2 * 2 ^ 169 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 169 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g10243 : 10243 ∈ P := S2 10243 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 10243 (by norm_num))
    have g223439473 : 223439473 ∈ P := S2 223439473 prime_223439473 (by norm_num) (hnz (by norm_num)) (R 223439473 (by norm_num))
    have g111719737 : 111719737 ∈ P := S1 111719737 prime_111719737 (by norm_num) (hnz (by norm_num)) 223439473 g223439473 (by norm_num)
    exact absurd (S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 10243 g10243 111719737 g111719737 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 571) h  -- d = 571: 5 | 73205584889+1, 57719+1
    rw [show (2:ℕ) ^ 571 = (2 ^ 200) ^ 2 * 2 ^ 171 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 171 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g73205584889 : 73205584889 ∈ P := S2 73205584889 prime_73205584889 (by norm_num) (hnz (by norm_num)) (R 73205584889 (by norm_num))
    have g57719 : 57719 ∈ P := S1 57719 (by norm_num) (by norm_num) (hnz (by norm_num)) 73205584889 g73205584889 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 73205584889 g73205584889 57719 g57719 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 577) h  -- d = 577: 5 | 2796392419+1, 479+1
    rw [show (2:ℕ) ^ 577 = (2 ^ 200) ^ 2 * 2 ^ 177 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 177 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2796392419 : 2796392419 ∈ P := S2 2796392419 prime_2796392419 (by norm_num) (hnz (by norm_num)) (R 2796392419 (by norm_num))
    have g479 : 479 ∈ P := S1 479 (by norm_num) (by norm_num) (hnz (by norm_num)) 2796392419 g2796392419 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2796392419 g2796392419 479 g479 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 587) h  -- d = 587: 7 | 13+1, 41+1
    rw [show (2:ℕ) ^ 587 = (2 ^ 200) ^ 2 * 2 ^ 187 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 187 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2769467 : 2769467 ∈ P := S2 2769467 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2769467 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 2769467 g2769467 (by norm_num)
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 2769467 g2769467 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 599) h  -- d = 599: 7^2 | 366994123+1
    rw [show (2:ℕ) ^ 599 = (2 ^ 200) ^ 2 * 2 ^ 199 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 199 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g366994123 : 366994123 ∈ P := S2 366994123 prime_366994123 (by norm_num) (hnz (by norm_num)) (R 366994123 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 366994123 g366994123 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 607) h  -- d = 607: 5^2 | 202769117249+1
    rw [show (2:ℕ) ^ 607 = (2 ^ 200) ^ 3 * 2 ^ 7 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 7 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g202769117249 : 202769117249 ∈ P := S2 202769117249 prime_202769117249 (by norm_num) (hnz (by norm_num)) (R 202769117249 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 202769117249 g202769117249 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 631) h  -- d = 631: 5 | 8309009+1, 2689+1
    rw [show (2:ℕ) ^ 631 = (2 ^ 200) ^ 3 * 2 ^ 31 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 31 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8309009 : 8309009 ∈ P := S2 8309009 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8309009 (by norm_num))
    have g2689 : 2689 ∈ P := S1 2689 (by norm_num) (by norm_num) (hnz (by norm_num)) 8309009 g8309009 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 8309009 g8309009 2689 g2689 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 641) h  -- d = 641: 31 | 353833+1, 61+1
    rw [show (2:ℕ) ^ 641 = (2 ^ 200) ^ 3 * 2 ^ 41 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 41 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g353833 : 353833 ∈ P := S2 353833 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 353833 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 353833 g353833 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 647) h  -- d = 647: 5 | 4570409+1, 9021769+1
    rw [show (2:ℕ) ^ 647 = (2 ^ 200) ^ 3 * 2 ^ 47 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 47 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4570409 : 4570409 ∈ P := S2 4570409 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4570409 (by norm_num))
    have g9021769 : 9021769 ∈ P := S2 9021769 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 9021769 (by norm_num))
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4570409 g4570409 9021769 g9021769 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 659) h  -- d = 659: 7^2 | 284689+1
    rw [show (2:ℕ) ^ 659 = (2 ^ 200) ^ 3 * 2 ^ 59 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 59 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g284689 : 284689 ∈ P := S2 284689 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 284689 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 284689 g284689 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 661) h  -- d = 661: 7 | 206233+1, 4611137+1
    rw [show (2:ℕ) ^ 661 = (2 ^ 200) ^ 3 * 2 ^ 61 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 61 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g206233 : 206233 ∈ P := S2 206233 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 206233 (by norm_num))
    have g4611137 : 4611137 ∈ P := S2 4611137 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4611137 (by norm_num))
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 206233 g206233 4611137 g4611137 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 677) h  -- d = 677: 5 | 2920579+1, 6190489+1
    rw [show (2:ℕ) ^ 677 = (2 ^ 200) ^ 3 * 2 ^ 77 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 77 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2920579 : 2920579 ∈ P := S2 2920579 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2920579 (by norm_num))
    have g6190489 : 6190489 ∈ P := S2 6190489 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6190489 (by norm_num))
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2920579 g2920579 6190489 g6190489 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 683) h  -- d = 683: 5^2 | 14449+1
    rw [show (2:ℕ) ^ 683 = (2 ^ 200) ^ 3 * 2 ^ 83 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 83 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1676083 : 1676083 ∈ P := S2 1676083 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1676083 (by norm_num))
    have g14449 : 14449 ∈ P := S1 14449 (by norm_num) (by norm_num) (hnz (by norm_num)) 1676083 g1676083 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 14449 g14449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 709) h  -- d = 709: 3^6 | (2^709+1) prod (p+1), p in {263, 647}
    rw [show (2:ℕ) ^ 709 = (2 ^ 200) ^ 3 * 2 ^ 109 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 109 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g340321 : 340321 ∈ P := S2 340321 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 340321 (by norm_num))
    have g263 : 263 ∈ P := S1 263 (by norm_num) (by norm_num) (hnz (by norm_num)) 340321 g340321 (by norm_num)
    have g647 : 647 ∈ P := S1 647 (by norm_num) (by norm_num) (hnz (by norm_num)) 340321 g340321 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g263 (by simp) (by norm_num : 3 ^ 1 ∣ 263 + 1)
    have b2 := bud_cons b1 g647 (by simp) (by norm_num : 3 ^ 4 ∣ 647 + 1)
    exact budget_kernel3 hP h3P E b2.1 ((pow_dvd_pow 3 (by norm_num)).trans b2.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 727) h  -- d = 727: 7 | 11633+1, 139+1
    rw [show (2:ℕ) ^ 727 = (2 ^ 200) ^ 3 * 2 ^ 127 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 127 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g11633 : 11633 ∈ P := S2 11633 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11633 (by norm_num))
    have g277 : 277 ∈ P := S1 277 (by norm_num) (by norm_num) (hnz (by norm_num)) 11633 g11633 (by norm_num)
    have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 277 g277 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 11633 g11633 139 g139 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 743) h  -- d = 743: 5 | 4343579+1, 59+1
    rw [show (2:ℕ) ^ 743 = (2 ^ 200) ^ 3 * 2 ^ 143 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 143 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4343579 : 4343579 ∈ P := S2 4343579 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4343579 (by norm_num))
    have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 4343579 g4343579 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4343579 g4343579 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 751) h  -- d = 751: 11 | 274867+1, 6247+1
    rw [show (2:ℕ) ^ 751 = (2 ^ 200) ^ 3 * 2 ^ 151 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 151 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g274867 : 274867 ∈ P := S2 274867 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 274867 (by norm_num))
    have g6247 : 6247 ∈ P := S1 6247 (by norm_num) (by norm_num) (hnz (by norm_num)) 274867 g274867 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 274867 g274867 6247 g6247 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 787) h  -- d = 787: 7^2 | 97+1
    rw [show (2:ℕ) ^ 787 = (2 ^ 200) ^ 3 * 2 ^ 187 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 187 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g942827 : 942827 ∈ P := S2 942827 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 942827 (by norm_num))
    have g78569 : 78569 ∈ P := S1 78569 (by norm_num) (by norm_num) (hnz (by norm_num)) 942827 g942827 (by norm_num)
    have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 78569 g78569 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 797) h  -- d = 797: 3^7 | (2^797+1) prod (p+1), p in {16829, 5, 11, 17}
    rw [show (2:ℕ) ^ 797 = (2 ^ 200) ^ 3 * 2 ^ 197 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 197 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g875107 : 875107 ∈ P := S2 875107 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 875107 (by norm_num))
    have g16829 : 16829 ∈ P := S1 16829 (by norm_num) (by norm_num) (hnz (by norm_num)) 875107 g875107 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 16829 g16829 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 16829 g16829 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 16829 g16829 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g16829 (by simp) (by norm_num : 3 ^ 2 ∣ 16829 + 1)
    have b2 := bud_cons b1 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b3 := bud_cons b2 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b4 := bud_cons b3 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 807) h  -- d = 807: 5^2 | 11299+1
    rw [show (2:ℕ) ^ 807 = (2 ^ 200) ^ 4 * 2 ^ 7 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 7 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g11299 : 11299 ∈ P := S2 11299 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11299 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 11299 g11299 (by norm_num)

set_option maxHeartbeats 22000000 in
theorem odd_1 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d ∈ ({809, 813, 821, 823, 853, 859, 881, 883, 887, 919, 929, 933, 937, 941, 947, 953, 967, 971, 977,
      991, 997, 1009, 1013, 1021, 1041, 1049, 1093, 1097, 1119, 1151, 1153, 1171, 1181, 1193,
      1223, 1227, 1237, 1249, 1257, 1263, 1277, 1279, 1283, 1289, 1291, 1307, 1319, 1327, 1345,
      1355} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 809) h  -- d = 809: 11 | 14563+1, 601897+1
    rw [show (2:ℕ) ^ 809 = (2 ^ 200) ^ 4 * 2 ^ 9 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 9 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14563 : 14563 ∈ P := S2 14563 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14563 (by norm_num))
    have g601897 : 601897 ∈ P := S2 601897 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 601897 (by norm_num))
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 14563 g14563 601897 g601897 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 813) h  -- d = 813: 7^2 | 112601+1
    rw [show (2:ℕ) ^ 813 = (2 ^ 200) ^ 4 * 2 ^ 13 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 13 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g450403 : 450403 ∈ P := S2 450403 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 450403 (by norm_num))
    have g112601 : 112601 ∈ P := S1 112601 (by norm_num) (by norm_num) (hnz (by norm_num)) 450403 g450403 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 112601 g112601 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 821) h  -- d = 821: 5 | 6569+1, 19+1
    rw [show (2:ℕ) ^ 821 = (2 ^ 200) ^ 4 * 2 ^ 21 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 21 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6569 : 6569 ∈ P := S2 6569 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6569 (by norm_num))
    have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 6569 g6569 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 6569 g6569 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 823) h  -- d = 823: 7 | 158017+1, 83+1
    rw [show (2:ℕ) ^ 823 = (2 ^ 200) ^ 4 * 2 ^ 23 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 23 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g316033 : 316033 ∈ P := S2 316033 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 316033 (by norm_num))
    have g158017 : 158017 ∈ P := S1 158017 (by norm_num) (by norm_num) (hnz (by norm_num)) 316033 g316033 (by norm_num)
    have g11287 : 11287 ∈ P := S1 11287 (by norm_num) (by norm_num) (hnz (by norm_num)) 158017 g158017 (by norm_num)
    have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 11287 g11287 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 158017 g158017 83 g83 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 853) h  -- d = 853: 3^6 | (2^853+1) prod (p+1), p in {2465171, 68477, 101, 113}
    rw [show (2:ℕ) ^ 853 = (2 ^ 200) ^ 4 * 2 ^ 53 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 53 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2465171 : 2465171 ∈ P := S2 2465171 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2465171 (by norm_num))
    have g68477 : 68477 ∈ P := S1 68477 (by norm_num) (by norm_num) (hnz (by norm_num)) 2465171 g2465171 (by norm_num)
    have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 68477 g68477 (by norm_num)
    have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 68477 g68477 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g2465171 (by simp) (by norm_num : 3 ^ 2 ∣ 2465171 + 1)
    have b2 := bud_cons b1 g68477 (by simp) (by norm_num : 3 ^ 1 ∣ 68477 + 1)
    have b3 := bud_cons b2 g101 (by simp) (by norm_num : 3 ^ 1 ∣ 101 + 1)
    have b4 := bud_cons b3 g113 (by simp) (by norm_num : 3 ^ 1 ∣ 113 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 859) h  -- d = 859: 5^2 | 499+1
    rw [show (2:ℕ) ^ 859 = (2 ^ 200) ^ 4 * 2 ^ 59 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 59 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4045891 : 4045891 ∈ P := S2 4045891 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4045891 (by norm_num))
    have g499 : 499 ∈ P := S1 499 (by norm_num) (by norm_num) (hnz (by norm_num)) 4045891 g4045891 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 499 g499 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 881) h  -- d = 881: 5^2 | 42295049+1
    rw [show (2:ℕ) ^ 881 = (2 ^ 200) ^ 4 * 2 ^ 81 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 81 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g42295049 : 42295049 ∈ P := S2 42295049 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 42295049 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 42295049 g42295049 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 883) h  -- d = 883: 7 | 294923+1, 10597+1
    rw [show (2:ℕ) ^ 883 = (2 ^ 200) ^ 4 * 2 ^ 83 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 83 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g294923 : 294923 ∈ P := S2 294923 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 294923 (by norm_num))
    have g21193 : 21193 ∈ P := S2 21193 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 21193 (by norm_num))
    have g10597 : 10597 ∈ P := S1 10597 (by norm_num) (by norm_num) (hnz (by norm_num)) 21193 g21193 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 294923 g294923 10597 g10597 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 887) h  -- d = 887: 11^2 | 5323+1
    rw [show (2:ℕ) ^ 887 = (2 ^ 200) ^ 4 * 2 ^ 87 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 87 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5323 : 5323 ∈ P := S2 5323 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5323 (by norm_num))
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 5323 g5323 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 919) h  -- d = 919: 5^2 | 118799+1
    rw [show (2:ℕ) ^ 919 = (2 ^ 200) ^ 4 * 2 ^ 119 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 119 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14968673 : 14968673 ∈ P := S2 14968673 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14968673 (by norm_num))
    have g118799 : 118799 ∈ P := S1 118799 (by norm_num) (by norm_num) (hnz (by norm_num)) 14968673 g14968673 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 118799 g118799 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 929) h  -- d = 929: 5 | 19+1, 1619+1
    rw [show (2:ℕ) ^ 929 = (2 ^ 200) ^ 4 * 2 ^ 129 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 129 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8243947 : 8243947 ∈ P := S2 8243947 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8243947 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 8243947 g8243947 (by norm_num)
    have g1619 : 1619 ∈ P := S1 1619 (by norm_num) (by norm_num) (hnz (by norm_num)) 8243947 g8243947 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 1619 g1619 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 933) h  -- d = 933: 19^2 | 30323+1
    rw [show (2:ℕ) ^ 933 = (2 ^ 200) ^ 4 * 2 ^ 133 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 133 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g121291 : 121291 ∈ P := S2 121291 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 121291 (by norm_num))
    have g30323 : 30323 ∈ P := S1 30323 (by norm_num) (by norm_num) (hnz (by norm_num)) 121291 g121291 (by norm_num)
    exact S6 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 30323 g30323 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 937) h  -- d = 937: 5 | 20795779+1, 40172939+1
    rw [show (2:ℕ) ^ 937 = (2 ^ 200) ^ 4 * 2 ^ 137 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 137 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g20795779 : 20795779 ∈ P := S2 20795779 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 20795779 (by norm_num))
    have g40172939 : 40172939 ∈ P := S2 40172939 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 40172939 (by norm_num))
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 20795779 g20795779 40172939 g40172939 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 941) h  -- d = 941: 5 | 1738969+1, 19+1
    rw [show (2:ℕ) ^ 941 = (2 ^ 200) ^ 4 * 2 ^ 141 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 141 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1738969 : 1738969 ∈ P := S2 1738969 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1738969 (by norm_num))
    have g173897 : 173897 ∈ P := S1 173897 (by norm_num) (by norm_num) (hnz (by norm_num)) 1738969 g1738969 (by norm_num)
    have g9661 : 9661 ∈ P := S1 9661 (by norm_num) (by norm_num) (hnz (by norm_num)) 173897 g173897 (by norm_num)
    have g4831 : 4831 ∈ P := S1 4831 (by norm_num) (by norm_num) (hnz (by norm_num)) 9661 g9661 (by norm_num)
    have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 4831 g4831 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 g151 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1738969 g1738969 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 947) h  -- d = 947: 3^7 | (2^947+1) prod (p+1), p in {7577, 13259, 5, 17}
    rw [show (2:ℕ) ^ 947 = (2 ^ 200) ^ 4 * 2 ^ 147 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 147 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7577 : 7577 ∈ P := S2 7577 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7577 (by norm_num))
    have g13259 : 13259 ∈ P := S2 13259 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13259 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 13259 g13259 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 13259 g13259 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g7577 (by simp) (by norm_num : 3 ^ 2 ∣ 7577 + 1)
    have b2 := bud_cons b1 g13259 (by simp) (by norm_num : 3 ^ 1 ∣ 13259 + 1)
    have b3 := bud_cons b2 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b4 := bud_cons b3 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 953) h  -- d = 953: 3^6 | (2^953+1) prod (p+1), p in {1907, 53}
    rw [show (2:ℕ) ^ 953 = (2 ^ 200) ^ 4 * 2 ^ 153 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 153 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1907 : 1907 ∈ P := S2 1907 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1907 (by norm_num))
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 1907 g1907 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g1907 (by simp) (by norm_num : 3 ^ 2 ∣ 1907 + 1)
    have b2 := bud_cons b1 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b2.1 ((pow_dvd_pow 3 (by norm_num)).trans b2.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 967) h  -- d = 967: 3^6 | (2^967+1) prod (p+1), p in {47, 4691, 17, 23}
    rw [show (2:ℕ) ^ 967 = (2 ^ 200) ^ 4 * 2 ^ 167 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 167 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g440953 : 440953 ∈ P := S2 440953 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 440953 (by norm_num))
    have g47 : 47 ∈ P := S1 47 (by norm_num) (by norm_num) (hnz (by norm_num)) 440953 g440953 (by norm_num)
    have g4691 : 4691 ∈ P := S1 4691 (by norm_num) (by norm_num) (hnz (by norm_num)) 440953 g440953 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 4691 g4691 (by norm_num)
    have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 4691 g4691 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g47 (by simp) (by norm_num : 3 ^ 1 ∣ 47 + 1)
    have b2 := bud_cons b1 g4691 (by simp) (by norm_num : 3 ^ 1 ∣ 4691 + 1)
    have b3 := bud_cons b2 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b4 := bud_cons b3 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 971) h  -- d = 971: 7 | 181+1, 13+1
    rw [show (2:ℕ) ^ 971 = (2 ^ 200) ^ 4 * 2 ^ 171 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 171 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g495211 : 495211 ∈ P := S2 495211 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 495211 (by norm_num))
    have g123803 : 123803 ∈ P := S1 123803 (by norm_num) (by norm_num) (hnz (by norm_num)) 495211 g495211 (by norm_num)
    have g181 : 181 ∈ P := S1 181 (by norm_num) (by norm_num) (hnz (by norm_num)) 123803 g123803 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 977) h  -- d = 977: 3^7 | (2^977+1) prod (p+1), p in {7817, 728843, 60737, 53}
    rw [show (2:ℕ) ^ 977 = (2 ^ 200) ^ 4 * 2 ^ 177 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 177 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7817 : 7817 ∈ P := S2 7817 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7817 (by norm_num))
    have g728843 : 728843 ∈ P := S2 728843 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 728843 (by norm_num))
    have g60737 : 60737 ∈ P := S1 60737 (by norm_num) (by norm_num) (hnz (by norm_num)) 728843 g728843 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 60737 g60737 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g7817 (by simp) (by norm_num : 3 ^ 1 ∣ 7817 + 1)
    have b2 := bud_cons b1 g728843 (by simp) (by norm_num : 3 ^ 1 ∣ 728843 + 1)
    have b3 := bud_cons b2 g60737 (by simp) (by norm_num : 3 ^ 1 ∣ 60737 + 1)
    have b4 := bud_cons b3 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 991) h  -- d = 991: 5 | 3060209+1, 1229+1
    rw [show (2:ℕ) ^ 991 = (2 ^ 200) ^ 4 * 2 ^ 191 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 191 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3060209 : 3060209 ∈ P := S2 3060209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3060209 (by norm_num))
    have g1229 : 1229 ∈ P := S1 1229 (by norm_num) (by norm_num) (hnz (by norm_num)) 3060209 g3060209 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3060209 g3060209 1229 g1229 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 997) h  -- d = 997: 61 | 3^5+1, 853+1
    rw [show (2:ℕ) ^ 997 = (2 ^ 200) ^ 4 * 2 ^ 197 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 197 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g614153 : 614153 ∈ P := S2 614153 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 614153 (by norm_num))
    have g102359 : 102359 ∈ P := S1 102359 (by norm_num) (by norm_num) (hnz (by norm_num)) 614153 g614153 (by norm_num)
    have g853 : 853 ∈ P := S1 853 (by norm_num) (by norm_num) (hnz (by norm_num)) 102359 g102359 (by norm_num)
    exact S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 853 g853 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1009) h  -- d = 1009: 11 | 962587+1, 131+1
    rw [show (2:ℕ) ^ 1009 = (2 ^ 200) ^ 5 * 2 ^ 9 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 9 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g962587 : 962587 ∈ P := S2 962587 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 962587 (by norm_num))
    have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 962587 g962587 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 962587 g962587 131 g131 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1013) h  -- d = 1013: 13^2 | 2027+1
    rw [show (2:ℕ) ^ 1013 = (2 ^ 200) ^ 5 * 2 ^ 13 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 13 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2027 : 2027 ∈ P := S2 2027 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2027 (by norm_num))
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 2027 g2027 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1021) h  -- d = 1021: 5 | 18379+1, 919+1
    rw [show (2:ℕ) ^ 1021 = (2 ^ 200) ^ 5 * 2 ^ 21 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 21 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g18379 : 18379 ∈ P := S2 18379 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 18379 (by norm_num))
    have g919 : 919 ∈ P := S1 919 (by norm_num) (by norm_num) (hnz (by norm_num)) 18379 g18379 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 18379 g18379 919 g919 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1041) h  -- d = 1041: 61 | 3^5+1, 6709+1
    rw [show (2:ℕ) ^ 1041 = (2 ^ 200) ^ 5 * 2 ^ 41 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 41 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14865481 : 14865481 ∈ P := S2 14865481 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14865481 (by norm_num))
    have g26833 : 26833 ∈ P := S1 26833 (by norm_num) (by norm_num) (hnz (by norm_num)) 14865481 g14865481 (by norm_num)
    have g13417 : 13417 ∈ P := S1 13417 (by norm_num) (by norm_num) (hnz (by norm_num)) 26833 g26833 (by norm_num)
    have g6709 : 6709 ∈ P := S1 6709 (by norm_num) (by norm_num) (hnz (by norm_num)) 13417 g13417 (by norm_num)
    exact S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 6709 g6709 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1049) h  -- d = 1049: 5^2 | 2099+1
    rw [show (2:ℕ) ^ 1049 = (2 ^ 200) ^ 5 * 2 ^ 49 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 49 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2099 : 2099 ∈ P := S2 2099 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2099 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2099 g2099 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1093) h  -- d = 1093: 11 | 306041+1, 43+1
    rw [show (2:ℕ) ^ 1093 = (2 ^ 200) ^ 5 * 2 ^ 93 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 93 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g306041 : 306041 ∈ P := S2 306041 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 306041 (by norm_num))
    have g4637 : 4637 ∈ P := S1 4637 (by norm_num) (by norm_num) (hnz (by norm_num)) 306041 g306041 (by norm_num)
    have g773 : 773 ∈ P := S1 773 (by norm_num) (by norm_num) (hnz (by norm_num)) 4637 g4637 (by norm_num)
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 773 g773 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 306041 g306041 43 g43 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1097) h  -- d = 1097: 13^2 | 1237417+1
    rw [show (2:ℕ) ^ 1097 = (2 ^ 200) ^ 5 * 2 ^ 97 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 97 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1237417 : 1237417 ∈ P := S2 1237417 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1237417 (by norm_num))
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1237417 g1237417 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1119) h  -- d = 1119: 3^6 | (2^1119+1) prod (p+1), p in {15107, 1259, 5}
    rw [show (2:ℕ) ^ 1119 = (2 ^ 200) ^ 5 * 2 ^ 119 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 119 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g60427 : 60427 ∈ P := S2 60427 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 60427 (by norm_num))
    have g15107 : 15107 ∈ P := S1 15107 (by norm_num) (by norm_num) (hnz (by norm_num)) 60427 g60427 (by norm_num)
    have g1259 : 1259 ∈ P := S1 1259 (by norm_num) (by norm_num) (hnz (by norm_num)) 15107 g15107 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1259 g1259 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 2 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 2) (by norm_num))⟩
    have b1 := bud_cons b0 g15107 (by simp) (by norm_num : 3 ^ 1 ∣ 15107 + 1)
    have b2 := bud_cons b1 g1259 (by simp) (by norm_num : 3 ^ 2 ∣ 1259 + 1)
    have b3 := bud_cons b2 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1151) h  -- d = 1151: 7 | 307+1, 13+1
    rw [show (2:ℕ) ^ 1151 = (2 ^ 200) ^ 5 * 2 ^ 151 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 151 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g9209 : 9209 ∈ P := S2 9209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 9209 (by norm_num))
    have g307 : 307 ∈ P := S1 307 (by norm_num) (by norm_num) (hnz (by norm_num)) 9209 g9209 (by norm_num)
    have g264731 : 264731 ∈ P := S2 264731 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 264731 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 264731 g264731 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 307 g307 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1153) h  -- d = 1153: 3^6 | (2^1153+1) prod (p+1), p in {101, 137, 17, 23}
    rw [show (2:ℕ) ^ 1153 = (2 ^ 200) ^ 5 * 2 ^ 153 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 153 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g27673 : 27673 ∈ P := S2 27673 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 27673 (by norm_num))
    have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 27673 g27673 (by norm_num)
    have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 27673 g27673 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 101 g101 (by norm_num)
    have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g101 (by simp) (by norm_num : 3 ^ 1 ∣ 101 + 1)
    have b2 := bud_cons b1 g137 (by simp) (by norm_num : 3 ^ 1 ∣ 137 + 1)
    have b3 := bud_cons b2 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b4 := bud_cons b3 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1171) h  -- d = 1171: 19 | 25763+1, 113+1
    rw [show (2:ℕ) ^ 1171 = (2 ^ 200) ^ 5 * 2 ^ 171 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 171 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g25763 : 25763 ∈ P := S2 25763 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 25763 (by norm_num))
    have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 25763 g25763 (by norm_num)
    exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 25763 g25763 113 g113 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1181) h  -- d = 1181: 19 | 59051+1, 37+1
    rw [show (2:ℕ) ^ 1181 = (2 ^ 200) ^ 5 * 2 ^ 181 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 181 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g59051 : 59051 ∈ P := S2 59051 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 59051 (by norm_num))
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 59051 g59051 (by norm_num)
    exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 59051 g59051 37 g37 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1193) h  -- d = 1193: 7^2 | 4507+1
    rw [show (2:ℕ) ^ 1193 = (2 ^ 200) ^ 5 * 2 ^ 193 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 193 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g324497 : 324497 ∈ P := S2 324497 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 324497 (by norm_num))
    have g54083 : 54083 ∈ P := S1 54083 (by norm_num) (by norm_num) (hnz (by norm_num)) 324497 g324497 (by norm_num)
    have g4507 : 4507 ∈ P := S1 4507 (by norm_num) (by norm_num) (hnz (by norm_num)) 54083 g54083 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 4507 g4507 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1223) h  -- d = 1223: 5 | 594379+1, 19+1
    rw [show (2:ℕ) ^ 1223 = (2 ^ 200) ^ 6 * 2 ^ 23 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 23 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g594379 : 594379 ∈ P := S2 594379 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 594379 (by norm_num))
    have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 594379 g594379 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 113 g113 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 594379 g594379 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1227) h  -- d = 1227: 5^2 | 2422099+1
    rw [show (2:ℕ) ^ 1227 = (2 ^ 200) ^ 6 * 2 ^ 27 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 27 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2422099 : 2422099 ∈ P := S2 2422099 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2422099 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2422099 g2422099 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1237) h  -- d = 1237: 5^2 | 3299+1
    rw [show (2:ℕ) ^ 1237 = (2 ^ 200) ^ 6 * 2 ^ 37 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 37 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g19793 : 19793 ∈ P := S2 19793 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 19793 (by norm_num))
    have g3299 : 3299 ∈ P := S1 3299 (by norm_num) (by norm_num) (hnz (by norm_num)) 19793 g19793 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3299 g3299 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1249) h  -- d = 1249: 5 | 3539+1, 59+1
    rw [show (2:ℕ) ^ 1249 = (2 ^ 200) ^ 6 * 2 ^ 49 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 49 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g42467 : 42467 ∈ P := S2 42467 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 42467 (by norm_num))
    have g3539 : 3539 ∈ P := S1 3539 (by norm_num) (by norm_num) (hnz (by norm_num)) 42467 g42467 (by norm_num)
    have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 3539 g3539 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3539 g3539 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1257) h  -- d = 1257: 5 | 89+1, 19+1
    rw [show (2:ℕ) ^ 1257 = (2 ^ 200) ^ 6 * 2 ^ 57 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 57 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g20113 : 20113 ∈ P := S2 20113 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 20113 (by norm_num))
    have g89 : 89 ∈ P := S1 89 (by norm_num) (by norm_num) (hnz (by norm_num)) 20113 g20113 (by norm_num)
    have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 20113 g20113 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 113 g113 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 89 g89 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1263) h  -- d = 1263: 3^6 | (2^1263+1) prod (p+1), p in {4211}
    rw [show (2:ℕ) ^ 1263 = (2 ^ 200) ^ 6 * 2 ^ 63 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 63 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4211 : 4211 ∈ P := S2 4211 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4211 (by norm_num))
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 2 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 2) (by norm_num))⟩
    have b1 := bud_cons b0 g4211 (by simp) (by norm_num : 3 ^ 4 ∣ 4211 + 1)
    exact budget_kernel3 hP h3P E b1.1 ((pow_dvd_pow 3 (by norm_num)).trans b1.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1277) h  -- d = 1277: 5 | 19+1, 439+1
    rw [show (2:ℕ) ^ 1277 = (2 ^ 200) ^ 6 * 2 ^ 77 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 77 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3432577 : 3432577 ∈ P := S2 3432577 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3432577 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 3432577 g3432577 (by norm_num)
    have g877 : 877 ∈ P := S1 877 (by norm_num) (by norm_num) (hnz (by norm_num)) 3432577 g3432577 (by norm_num)
    have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 877 g877 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 439 g439 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1279) h  -- d = 1279: 7^2 | 3107971+1
    rw [show (2:ℕ) ^ 1279 = (2 ^ 200) ^ 6 * 2 ^ 79 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 79 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3107971 : 3107971 ∈ P := S2 3107971 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3107971 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 3107971 g3107971 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1283) h  -- d = 1283: 5^2 | 7699+1
    rw [show (2:ℕ) ^ 1283 = (2 ^ 200) ^ 6 * 2 ^ 83 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 83 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7699 : 7699 ∈ P := S2 7699 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7699 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 7699 g7699 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1289) h  -- d = 1289: 31 | 30937+1, 61+1
    rw [show (2:ℕ) ^ 1289 = (2 ^ 200) ^ 6 * 2 ^ 89 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 89 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g30937 : 30937 ∈ P := S2 30937 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 30937 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 30937 g30937 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1291) h  -- d = 1291: 3^6 | (2^1291+1) prod (p+1), p in {28403, 263, 11}
    rw [show (2:ℕ) ^ 1291 = (2 ^ 200) ^ 6 * 2 ^ 91 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 91 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g28403 : 28403 ∈ P := S2 28403 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 28403 (by norm_num))
    have g263 : 263 ∈ P := S1 263 (by norm_num) (by norm_num) (hnz (by norm_num)) 28403 g28403 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 263 g263 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g28403 (by simp) (by norm_num : 3 ^ 3 ∣ 28403 + 1)
    have b2 := bud_cons b1 g263 (by simp) (by norm_num : 3 ^ 1 ∣ 263 + 1)
    have b3 := bud_cons b2 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1307) h  -- d = 1307: 7 | 10457+1, 83+1
    rw [show (2:ℕ) ^ 1307 = (2 ^ 200) ^ 6 * 2 ^ 107 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 107 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g10457 : 10457 ∈ P := S2 10457 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 10457 (by norm_num))
    have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 10457 g10457 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 10457 g10457 83 g83 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1319) h  -- d = 1319: 5^2 | 1399+1
    rw [show (2:ℕ) ^ 1319 = (2 ^ 200) ^ 6 * 2 ^ 119 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 119 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g11142913 : 11142913 ∈ P := S2 11142913 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11142913 (by norm_num))
    have g5571457 : 5571457 ∈ P := S1 5571457 (by norm_num) (by norm_num) (hnz (by norm_num)) 11142913 g11142913 (by norm_num)
    have g33563 : 33563 ∈ P := S1 33563 (by norm_num) (by norm_num) (hnz (by norm_num)) 5571457 g5571457 (by norm_num)
    have g2797 : 2797 ∈ P := S1 2797 (by norm_num) (by norm_num) (hnz (by norm_num)) 33563 g33563 (by norm_num)
    have g1399 : 1399 ∈ P := S1 1399 (by norm_num) (by norm_num) (hnz (by norm_num)) 2797 g2797 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1399 g1399 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1327) h  -- d = 1327: 7 | 181+1, 13+1
    rw [show (2:ℕ) ^ 1327 = (2 ^ 200) ^ 6 * 2 ^ 127 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 127 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7963 : 7963 ∈ P := S2 7963 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7963 (by norm_num))
    have g181 : 181 ∈ P := S1 181 (by norm_num) (by norm_num) (hnz (by norm_num)) 7963 g7963 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1345) h  -- d = 1345: 61 | 3^5+1, 2679241+1
    rw [show (2:ℕ) ^ 1345 = (2 ^ 200) ^ 6 * 2 ^ 145 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 145 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2679241 : 2679241 ∈ P := S2 2679241 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2679241 (by norm_num))
    exact S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 2679241 g2679241 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1355) h  -- d = 1355: 11 | 2^1355+1, 1627+1
    rw [show (2:ℕ) ^ 1355 = (2 ^ 200) ^ 6 * 2 ^ 155 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 155 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1627 : 1627 ∈ P := S2 1627 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1627 (by norm_num))
    exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11 (by norm_num)) 1627 g1627 (by norm_num)

set_option maxHeartbeats 22000000 in
theorem odd_2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d ∈ ({1361, 1367, 1399, 1427, 1439, 1451, 1461, 1481, 1483, 1487, 1493, 1499, 1509, 1527, 1531, 1555,
      1559, 1565, 1567, 1571, 1579, 1601, 1609, 1613, 1621, 1627, 1699, 1721, 1733, 1735, 1759,
      1765, 1779, 1789, 1803, 1823, 1839, 1857, 1865, 1871, 1897, 1901, 1915, 1933, 1949, 1973,
      1979, 2017, 2027, 2029} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1361) h  -- d = 1361: 11^2 | 10889+1
    rw [show (2:ℕ) ^ 1361 = (2 ^ 200) ^ 6 * 2 ^ 161 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 161 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g10889 : 10889 ∈ P := S2 10889 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 10889 (by norm_num))
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 10889 g10889 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1367) h  -- d = 1367: 5 | 688969+1, 29+1
    rw [show (2:ℕ) ^ 1367 = (2 ^ 200) ^ 6 * 2 ^ 167 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 167 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g688969 : 688969 ∈ P := S2 688969 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 688969 (by norm_num))
    have g68897 : 68897 ∈ P := S1 68897 (by norm_num) (by norm_num) (hnz (by norm_num)) 688969 g688969 (by norm_num)
    have g11483 : 11483 ∈ P := S1 11483 (by norm_num) (by norm_num) (hnz (by norm_num)) 68897 g68897 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 11483 g11483 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 688969 g688969 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1399) h  -- d = 1399: 7 | 13+1, 41+1
    rw [show (2:ℕ) ^ 1399 = (2 ^ 200) ^ 6 * 2 ^ 199 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 199 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g33577 : 33577 ∈ P := S2 33577 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 33577 (by norm_num))
    have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 33577 g33577 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
    have g163 : 163 ∈ P := S1 163 (by norm_num) (by norm_num) (hnz (by norm_num)) 33577 g33577 (by norm_num)
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 163 g163 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1427) h  -- d = 1427: 13 | 693523+1, 5628089+1
    rw [show (2:ℕ) ^ 1427 = (2 ^ 200) ^ 7 * 2 ^ 27 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 27 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g693523 : 693523 ∈ P := S2 693523 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 693523 (by norm_num))
    have g5628089 : 5628089 ∈ P := S2 5628089 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5628089 (by norm_num))
    exact absurd (S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 693523 g693523 5628089 g5628089 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1439) h  -- d = 1439: 13^2 | 5640881+1
    rw [show (2:ℕ) ^ 1439 = (2 ^ 200) ^ 7 * 2 ^ 39 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 39 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5640881 : 5640881 ∈ P := S2 5640881 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5640881 (by norm_num))
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 5640881 g5640881 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1451) h  -- d = 1451: 7 | 8707+1, 13+1
    rw [show (2:ℕ) ^ 1451 = (2 ^ 200) ^ 7 * 2 ^ 51 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 51 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8707 : 8707 ∈ P := S2 8707 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8707 (by norm_num))
    have g311 : 311 ∈ P := S1 311 (by norm_num) (by norm_num) (hnz (by norm_num)) 8707 g8707 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 311 g311 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 8707 g8707 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1461) h  -- d = 1461: 17 | 101+1, 373+1
    rw [show (2:ℕ) ^ 1461 = (2 ^ 200) ^ 7 * 2 ^ 61 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 61 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1054843 : 1054843 ∈ P := S2 1054843 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1054843 (by norm_num))
    have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 1054843 g1054843 (by norm_num)
    have g373 : 373 ∈ P := S1 373 (by norm_num) (by norm_num) (hnz (by norm_num)) 1054843 g1054843 (by norm_num)
    exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 101 g101 373 g373 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1481) h  -- d = 1481: 5 | 145139+1, 59+1
    rw [show (2:ℕ) ^ 1481 = (2 ^ 200) ^ 7 * 2 ^ 81 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 81 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g145139 : 145139 ∈ P := S2 145139 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 145139 (by norm_num))
    have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 145139 g145139 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 145139 g145139 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1483) h  -- d = 1483: 3^7 | (2^1483+1) prod (p+1), p in {31994243, 296243}
    rw [show (2:ℕ) ^ 1483 = (2 ^ 200) ^ 7 * 2 ^ 83 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 83 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g31994243 : 31994243 ∈ P := S2 31994243 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 31994243 (by norm_num))
    have g296243 : 296243 ∈ P := S1 296243 (by norm_num) (by norm_num) (hnz (by norm_num)) 31994243 g31994243 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g31994243 (by simp) (by norm_num : 3 ^ 3 ∣ 31994243 + 1)
    have b2 := bud_cons b1 g296243 (by simp) (by norm_num : 3 ^ 3 ∣ 296243 + 1)
    exact budget_kernel3 hP h3P E b2.1 ((pow_dvd_pow 3 (by norm_num)).trans b2.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1487) h  -- d = 1487: 3^6 | (2^1487+1) prod (p+1), p in {17, 41, 3917, 653}
    rw [show (2:ℕ) ^ 1487 = (2 ^ 200) ^ 7 * 2 ^ 87 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 87 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5112307 : 5112307 ∈ P := S2 5112307 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5112307 (by norm_num))
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 5112307 g5112307 (by norm_num)
    have g321193 : 321193 ∈ P := S2 321193 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 321193 (by norm_num))
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 321193 g321193 (by norm_num)
    have g3917 : 3917 ∈ P := S1 3917 (by norm_num) (by norm_num) (hnz (by norm_num)) 321193 g321193 (by norm_num)
    have g653 : 653 ∈ P := S1 653 (by norm_num) (by norm_num) (hnz (by norm_num)) 3917 g3917 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g41 (by simp) (by norm_num : 3 ^ 1 ∣ 41 + 1)
    have b3 := bud_cons b2 g3917 (by simp) (by norm_num : 3 ^ 1 ∣ 3917 + 1)
    have b4 := bud_cons b3 g653 (by simp) (by norm_num : 3 ^ 1 ∣ 653 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1493) h  -- d = 1493: 5^2 | 391249+1
    rw [show (2:ℕ) ^ 1493 = (2 ^ 200) ^ 7 * 2 ^ 93 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 93 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14084963 : 14084963 ∈ P := S2 14084963 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14084963 (by norm_num))
    have g391249 : 391249 ∈ P := S1 391249 (by norm_num) (by norm_num) (hnz (by norm_num)) 14084963 g14084963 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 391249 g391249 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1499) h  -- d = 1499: 17 | 2447+1, 67+1
    rw [show (2:ℕ) ^ 1499 = (2 ^ 200) ^ 7 * 2 ^ 99 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 99 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2143571 : 2143571 ∈ P := S2 2143571 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2143571 (by norm_num))
    have g2447 : 2447 ∈ P := S1 2447 (by norm_num) (by norm_num) (hnz (by norm_num)) 2143571 g2143571 (by norm_num)
    have g44971 : 44971 ∈ P := S2 44971 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 44971 (by norm_num))
    have g11243 : 11243 ∈ P := S1 11243 (by norm_num) (by norm_num) (hnz (by norm_num)) 44971 g44971 (by norm_num)
    have g937 : 937 ∈ P := S1 937 (by norm_num) (by norm_num) (hnz (by norm_num)) 11243 g11243 (by norm_num)
    have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 937 g937 (by norm_num)
    exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 2447 g2447 67 g67 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1509) h  -- d = 1509: 7^2 | 20127043+1
    rw [show (2:ℕ) ^ 1509 = (2 ^ 200) ^ 7 * 2 ^ 109 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 109 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g20127043 : 20127043 ∈ P := S2 20127043 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 20127043 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 20127043 g20127043 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1527) h  -- d = 1527: 5 | 1019+1, 139+1
    rw [show (2:ℕ) ^ 1527 = (2 ^ 200) ^ 7 * 2 ^ 127 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 127 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1019 : 1019 ∈ P := S2 1019 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1019 (by norm_num))
    have g1062793 : 1062793 ∈ P := S2 1062793 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1062793 (by norm_num))
    have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 1062793 g1062793 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1019 g1019 139 g139 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1531) h  -- d = 1531: 31 | 24260227+1, 61+1
    rw [show (2:ℕ) ^ 1531 = (2 ^ 200) ^ 7 * 2 ^ 131 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 131 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g24260227 : 24260227 ∈ P := S2 24260227 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 24260227 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 24260227 g24260227 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1555) h  -- d = 1555: 11 | 2^1555+1, 21911+1
    rw [show (2:ℕ) ^ 1555 = (2 ^ 200) ^ 7 * 2 ^ 155 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 155 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g16915291 : 16915291 ∈ P := S2 16915291 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16915291 (by norm_num))
    have g21911 : 21911 ∈ P := S1 21911 (by norm_num) (by norm_num) (hnz (by norm_num)) 16915291 g16915291 (by norm_num)
    exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11 (by norm_num)) 21911 g21911 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1559) h  -- d = 1559: 3^6 | (2^1559+1) prod (p+1), p in {12473, 11}
    rw [show (2:ℕ) ^ 1559 = (2 ^ 200) ^ 7 * 2 ^ 159 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 159 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g12473 : 12473 ∈ P := S2 12473 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 12473 (by norm_num))
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 12473 g12473 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g12473 (by simp) (by norm_num : 3 ^ 4 ∣ 12473 + 1)
    have b2 := bud_cons b1 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    exact budget_kernel3 hP h3P E b2.1 ((pow_dvd_pow 3 (by norm_num)).trans b2.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1565) h  -- d = 1565: 13 | 1032901+1, 39727+1
    rw [show (2:ℕ) ^ 1565 = (2 ^ 200) ^ 7 * 2 ^ 165 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 165 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2065801 : 2065801 ∈ P := S2 2065801 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2065801 (by norm_num))
    have g1032901 : 1032901 ∈ P := S1 1032901 (by norm_num) (by norm_num) (hnz (by norm_num)) 2065801 g2065801 (by norm_num)
    have g39727 : 39727 ∈ P := S1 39727 (by norm_num) (by norm_num) (hnz (by norm_num)) 1032901 g1032901 (by norm_num)
    exact absurd (S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1032901 g1032901 39727 g39727 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1567) h  -- d = 1567: 7^2 | 2351+1
    rw [show (2:ℕ) ^ 1567 = (2 ^ 200) ^ 7 * 2 ^ 167 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 167 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g9403 : 9403 ∈ P := S2 9403 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 9403 (by norm_num))
    have g2351 : 2351 ∈ P := S1 2351 (by norm_num) (by norm_num) (hnz (by norm_num)) 9403 g9403 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 2351 g2351 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1571) h  -- d = 1571: 5 | 12569+1, 419+1
    rw [show (2:ℕ) ^ 1571 = (2 ^ 200) ^ 7 * 2 ^ 171 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 171 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g12569 : 12569 ∈ P := S2 12569 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 12569 (by norm_num))
    have g419 : 419 ∈ P := S1 419 (by norm_num) (by norm_num) (hnz (by norm_num)) 12569 g12569 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 12569 g12569 419 g419 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1579) h  -- d = 1579: 7^2 | 97+1
    rw [show (2:ℕ) ^ 1579 = (2 ^ 200) ^ 7 * 2 ^ 179 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 179 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g34739 : 34739 ∈ P := S2 34739 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 34739 (by norm_num))
    have g193 : 193 ∈ P := S1 193 (by norm_num) (by norm_num) (hnz (by norm_num)) 34739 g34739 (by norm_num)
    have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 193 g193 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1601) h  -- d = 1601: 3^6 | (2^1601+1) prod (p+1), p in {3203, 89, 5}
    rw [show (2:ℕ) ^ 1601 = (2 ^ 200) ^ 8 * 2 ^ 1 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 1 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3203 : 3203 ∈ P := S2 3203 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3203 (by norm_num))
    have g89 : 89 ∈ P := S1 89 (by norm_num) (by norm_num) (hnz (by norm_num)) 3203 g3203 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 89 g89 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g3203 (by simp) (by norm_num : 3 ^ 2 ∣ 3203 + 1)
    have b2 := bud_cons b1 g89 (by simp) (by norm_num : 3 ^ 2 ∣ 89 + 1)
    have b3 := bud_cons b2 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1609) h  -- d = 1609: 5^2 | 149+1
    rw [show (2:ℕ) ^ 1609 = (2 ^ 200) ^ 8 * 2 ^ 9 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 9 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g16091 : 16091 ∈ P := S2 16091 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16091 (by norm_num))
    have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 16091 g16091 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1613) h  -- d = 1613: 5^2 | 3138899+1
    rw [show (2:ℕ) ^ 1613 = (2 ^ 200) ^ 8 * 2 ^ 13 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 13 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3138899 : 3138899 ∈ P := S2 3138899 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3138899 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3138899 g3138899 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1621) h  -- d = 1621: 5 | 29179+1, 2995609+1
    rw [show (2:ℕ) ^ 1621 = (2 ^ 200) ^ 8 * 2 ^ 21 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 21 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g29179 : 29179 ∈ P := S2 29179 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 29179 (by norm_num))
    have g2995609 : 2995609 ∈ P := S2 2995609 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2995609 (by norm_num))
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29179 g29179 2995609 g2995609 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1627) h  -- d = 1627: 5 | 5375609+1, 59729+1
    rw [show (2:ℕ) ^ 1627 = (2 ^ 200) ^ 8 * 2 ^ 27 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 27 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5375609 : 5375609 ∈ P := S2 5375609 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5375609 (by norm_num))
    have g59729 : 59729 ∈ P := S1 59729 (by norm_num) (by norm_num) (hnz (by norm_num)) 5375609 g5375609 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5375609 g5375609 59729 g59729 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1699) h  -- d = 1699: 3^8 | (2^1699+1) prod (p+1), p in {118931, 11, 17, 53}
    rw [show (2:ℕ) ^ 1699 = (2 ^ 200) ^ 8 * 2 ^ 99 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 99 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g118931 : 118931 ∈ P := S2 118931 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 118931 (by norm_num))
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 118931 g118931 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 118931 g118931 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 118931 g118931 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g118931 (by simp) (by norm_num : 3 ^ 1 ∣ 118931 + 1)
    have b2 := bud_cons b1 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b3 := bud_cons b2 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b4 := bud_cons b3 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1721) h  -- d = 1721: 7 | 2533313+1, 13+1
    rw [show (2:ℕ) ^ 1721 = (2 ^ 200) ^ 8 * 2 ^ 121 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 121 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2533313 : 2533313 ∈ P := S2 2533313 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2533313 (by norm_num))
    have g60317 : 60317 ∈ P := S1 60317 (by norm_num) (by norm_num) (hnz (by norm_num)) 2533313 g2533313 (by norm_num)
    have g1117 : 1117 ∈ P := S1 1117 (by norm_num) (by norm_num) (hnz (by norm_num)) 60317 g60317 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1117 g1117 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 2533313 g2533313 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1733) h  -- d = 1733: 17^2 | 3467+1
    rw [show (2:ℕ) ^ 1733 = (2 ^ 200) ^ 8 * 2 ^ 133 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 133 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3467 : 3467 ∈ P := S2 3467 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3467 (by norm_num))
    exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 3467 g3467 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1735) h  -- d = 1735: 11 | 2^1735+1, 166561+1
    rw [show (2:ℕ) ^ 1735 = (2 ^ 200) ^ 8 * 2 ^ 135 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 135 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g166561 : 166561 ∈ P := S2 166561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 166561 (by norm_num))
    exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11 (by norm_num)) 166561 g166561 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1759) h  -- d = 1759: 3^6 | (2^1759+1) prod (p+1), p in {15099257, 2516543, 17}
    rw [show (2:ℕ) ^ 1759 = (2 ^ 200) ^ 8 * 2 ^ 159 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 159 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g15099257 : 15099257 ∈ P := S2 15099257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 15099257 (by norm_num))
    have g2516543 : 2516543 ∈ P := S1 2516543 (by norm_num) (by norm_num) (hnz (by norm_num)) 15099257 g15099257 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 2516543 g2516543 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g15099257 (by simp) (by norm_num : 3 ^ 1 ∣ 15099257 + 1)
    have b2 := bud_cons b1 g2516543 (by simp) (by norm_num : 3 ^ 2 ∣ 2516543 + 1)
    have b3 := bud_cons b2 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1765) h  -- d = 1765: 13^2 | 31771+1
    rw [show (2:ℕ) ^ 1765 = (2 ^ 200) ^ 8 * 2 ^ 165 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 165 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g31771 : 31771 ∈ P := S2 31771 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 31771 (by norm_num))
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 31771 g31771 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1779) h  -- d = 1779: 5 | 39139+1, 19+1
    rw [show (2:ℕ) ^ 1779 = (2 ^ 200) ^ 8 * 2 ^ 179 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 179 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g39139 : 39139 ∈ P := S2 39139 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 39139 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 39139 g39139 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 39139 g39139 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1789) h  -- d = 1789: 7 | 42937+1, 318443+1
    rw [show (2:ℕ) ^ 1789 = (2 ^ 200) ^ 8 * 2 ^ 189 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 189 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g42937 : 42937 ∈ P := S2 42937 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 42937 (by norm_num))
    have g318443 : 318443 ∈ P := S2 318443 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 318443 (by norm_num))
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 42937 g42937 318443 g318443 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1803) h  -- d = 1803: 11^2 | 5807+1
    rw [show (2:ℕ) ^ 1803 = (2 ^ 200) ^ 9 * 2 ^ 3 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 3 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g16573177 : 16573177 ∈ P := S2 16573177 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16573177 (by norm_num))
    have g5807 : 5807 ∈ P := S1 5807 (by norm_num) (by norm_num) (hnz (by norm_num)) 16573177 g16573177 (by norm_num)
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 5807 g5807 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1823) h  -- d = 1823: 3^6 | (2^1823+1) prod (p+1), p in {5, 131, 167, 11, 137}
    rw [show (2:ℕ) ^ 1823 = (2 ^ 200) ^ 9 * 2 ^ 23 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 23 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g10939 : 10939 ∈ P := S2 10939 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 10939 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 10939 g10939 (by norm_num)
    have g43753 : 43753 ∈ P := S2 43753 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 43753 (by norm_num))
    have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 43753 g43753 (by norm_num)
    have g167 : 167 ∈ P := S1 167 (by norm_num) (by norm_num) (hnz (by norm_num)) 43753 g43753 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 131 g131 (by norm_num)
    have g547 : 547 ∈ P := S1 547 (by norm_num) (by norm_num) (hnz (by norm_num)) 10939 g10939 (by norm_num)
    have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b2 := bud_cons b1 g131 (by simp) (by norm_num : 3 ^ 1 ∣ 131 + 1)
    have b3 := bud_cons b2 g167 (by simp) (by norm_num : 3 ^ 1 ∣ 167 + 1)
    have b4 := bud_cons b3 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b5 := bud_cons b4 g137 (by simp) (by norm_num : 3 ^ 1 ∣ 137 + 1)
    exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1839) h  -- d = 1839: 7 | 14713+1, 13+1
    rw [show (2:ℕ) ^ 1839 = (2 ^ 200) ^ 9 * 2 ^ 39 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 39 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14713 : 14713 ∈ P := S2 14713 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14713 (by norm_num))
    have g55171 : 55171 ∈ P := S2 55171 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 55171 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 55171 g55171 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 14713 g14713 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1857) h  -- d = 1857: 5^2 | 14449+1
    rw [show (2:ℕ) ^ 1857 = (2 ^ 200) ^ 9 * 2 ^ 57 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 57 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2109553 : 2109553 ∈ P := S2 2109553 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2109553 (by norm_num))
    have g14449 : 14449 ∈ P := S1 14449 (by norm_num) (by norm_num) (hnz (by norm_num)) 2109553 g2109553 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 14449 g14449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1865) h  -- d = 1865: 3^6 | (2^1865+1) prod (p+1), p in {11, 15107, 1259, 5}
    rw [show (2:ℕ) ^ 1865 = (2 ^ 200) ^ 9 * 2 ^ 65 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 65 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g11 : 11 ∈ P := S2 11 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11 (by norm_num))
    have g60427 : 60427 ∈ P := S2 60427 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 60427 (by norm_num))
    have g15107 : 15107 ∈ P := S1 15107 (by norm_num) (by norm_num) (hnz (by norm_num)) 60427 g60427 (by norm_num)
    have g1259 : 1259 ∈ P := S1 1259 (by norm_num) (by norm_num) (hnz (by norm_num)) 15107 g15107 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1259 g1259 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b2 := bud_cons b1 g15107 (by simp) (by norm_num : 3 ^ 1 ∣ 15107 + 1)
    have b3 := bud_cons b2 g1259 (by simp) (by norm_num : 3 ^ 2 ∣ 1259 + 1)
    have b4 := bud_cons b3 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1871) h  -- d = 1871: 11 | 1313443+1, 439+1
    rw [show (2:ℕ) ^ 1871 = (2 ^ 200) ^ 9 * 2 ^ 71 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 71 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1313443 : 1313443 ∈ P := S2 1313443 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1313443 (by norm_num))
    have g29851 : 29851 ∈ P := S1 29851 (by norm_num) (by norm_num) (hnz (by norm_num)) 1313443 g1313443 (by norm_num)
    have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 29851 g29851 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 1313443 g1313443 439 g439 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1897) h  -- d = 1897: 11 | 43+1, 1627+1
    rw [show (2:ℕ) ^ 1897 = (2 ^ 200) ^ 9 * 2 ^ 97 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 97 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 43 (by norm_num))
    have g1627 : 1627 ∈ P := S2 1627 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1627 (by norm_num))
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 1627 g1627 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1901) h  -- d = 1901: 3^6 | (2^1901+1) prod (p+1), p in {3803, 317, 53}
    rw [show (2:ℕ) ^ 1901 = (2 ^ 200) ^ 9 * 2 ^ 101 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 101 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3803 : 3803 ∈ P := S2 3803 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3803 (by norm_num))
    have g317 : 317 ∈ P := S1 317 (by norm_num) (by norm_num) (hnz (by norm_num)) 3803 g3803 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 317 g317 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g3803 (by simp) (by norm_num : 3 ^ 1 ∣ 3803 + 1)
    have b2 := bud_cons b1 g317 (by simp) (by norm_num : 3 ^ 1 ∣ 317 + 1)
    have b3 := bud_cons b2 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1915) h  -- d = 1915: 13^2 | 11491+1
    rw [show (2:ℕ) ^ 1915 = (2 ^ 200) ^ 9 * 2 ^ 115 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 115 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g11491 : 11491 ∈ P := S2 11491 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11491 (by norm_num))
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 11491 g11491 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1933) h  -- d = 1933: 3^7 | (2^1933+1) prod (p+1), p in {53, 101, 17}
    rw [show (2:ℕ) ^ 1933 = (2 ^ 200) ^ 9 * 2 ^ 133 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 133 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g278353 : 278353 ∈ P := S2 278353 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 278353 (by norm_num))
    have g139177 : 139177 ∈ P := S1 139177 (by norm_num) (by norm_num) (hnz (by norm_num)) 278353 g278353 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 139177 g139177 (by norm_num)
    have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 139177 g139177 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 101 g101 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    have b2 := bud_cons b1 g101 (by simp) (by norm_num : 3 ^ 1 ∣ 101 + 1)
    have b3 := bud_cons b2 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1949) h  -- d = 1949: 5 | 1251259+1, 79+1
    rw [show (2:ℕ) ^ 1949 = (2 ^ 200) ^ 9 * 2 ^ 149 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 149 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1251259 : 1251259 ∈ P := S2 1251259 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1251259 (by norm_num))
    have g62563 : 62563 ∈ P := S1 62563 (by norm_num) (by norm_num) (hnz (by norm_num)) 1251259 g1251259 (by norm_num)
    have g15641 : 15641 ∈ P := S1 15641 (by norm_num) (by norm_num) (hnz (by norm_num)) 62563 g62563 (by norm_num)
    have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 15641 g15641 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1251259 g1251259 79 g79 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1973) h  -- d = 1973: 5^2 | 1235099+1
    rw [show (2:ℕ) ^ 1973 = (2 ^ 200) ^ 9 * 2 ^ 173 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 173 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1235099 : 1235099 ∈ P := S2 1235099 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1235099 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1235099 g1235099 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1979) h  -- d = 1979: 3^7 | (2^1979+1) prod (p+1), p in {8802593, 17}
    rw [show (2:ℕ) ^ 1979 = (2 ^ 200) ^ 9 * 2 ^ 179 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 179 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8802593 : 8802593 ∈ P := S2 8802593 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8802593 (by norm_num))
    have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 8802593 g8802593 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g8802593 (by simp) (by norm_num : 3 ^ 4 ∣ 8802593 + 1)
    have b2 := bud_cons b1 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    exact budget_kernel3 hP h3P E b2.1 ((pow_dvd_pow 3 (by norm_num)).trans b2.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2017) h  -- d = 2017: 31 | 2936753+1, 61+1
    rw [show (2:ℕ) ^ 2017 = (2 ^ 200) ^ 10 * 2 ^ 17 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 17 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2936753 : 2936753 ∈ P := S2 2936753 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2936753 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 2936753 g2936753 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2027) h  -- d = 2027: 13^2 | 3041+1
    rw [show (2:ℕ) ^ 2027 = (2 ^ 200) ^ 10 * 2 ^ 27 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 27 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g12163 : 12163 ∈ P := S2 12163 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 12163 (by norm_num))
    have g3041 : 3041 ∈ P := S1 3041 (by norm_num) (by norm_num) (hnz (by norm_num)) 12163 g12163 (by norm_num)
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 3041 g3041 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2029) h  -- d = 2029: 11 | 240437+1, 43+1
    rw [show (2:ℕ) ^ 2029 = (2 ^ 200) ^ 10 * 2 ^ 29 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 29 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g961747 : 961747 ∈ P := S2 961747 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 961747 (by norm_num))
    have g240437 : 240437 ∈ P := S1 240437 (by norm_num) (by norm_num) (hnz (by norm_num)) 961747 g961747 (by norm_num)
    have g3019153 : 3019153 ∈ P := S2 3019153 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3019153 (by norm_num))
    have g22531 : 22531 ∈ P := S1 22531 (by norm_num) (by norm_num) (hnz (by norm_num)) 3019153 g3019153 (by norm_num)
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 22531 g22531 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 240437 g240437 43 g43 (by norm_num) (by norm_num)) (by norm_num)

set_option maxHeartbeats 22000000 in
theorem odd_3 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d ∈ ({2045, 2069, 2081, 2095, 2099, 2103, 2105, 2129, 2153, 2157, 2177, 2191, 2199, 2217, 2221, 2237,
      2239, 2243, 2251, 2269, 2271, 2273, 2281, 2285, 2293, 2307, 2333, 2341, 2347, 2357, 2383,
      2399, 2435, 2441, 2447, 2471, 2477, 2503, 2517, 2543, 2545, 2549, 2571, 2579, 2589, 2593,
      2609, 2611, 2631, 2647} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2045) h  -- d = 2045: 11 | 2^2045+1, 4091+1
    rw [show (2:ℕ) ^ 2045 = (2 ^ 200) ^ 10 * 2 ^ 45 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 45 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4091 : 4091 ∈ P := S2 4091 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4091 (by norm_num))
    exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11 (by norm_num)) 4091 g4091 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2069) h  -- d = 2069: 31 | 16553+1, 61+1
    rw [show (2:ℕ) ^ 2069 = (2 ^ 200) ^ 10 * 2 ^ 69 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 69 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g16553 : 16553 ∈ P := S2 16553 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16553 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 16553 g16553 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2081) h  -- d = 2081: 5^2 | 16649+1
    rw [show (2:ℕ) ^ 2081 = (2 ^ 200) ^ 10 * 2 ^ 81 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 81 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g16649 : 16649 ∈ P := S2 16649 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16649 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 16649 g16649 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2095) h  -- d = 2095: 19 | 37+1, 151+1
    rw [show (2:ℕ) ^ 2095 = (2 ^ 200) ^ 10 * 2 ^ 95 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 95 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g33521 : 33521 ∈ P := S2 33521 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 33521 (by norm_num))
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 33521 g33521 (by norm_num)
    have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 33521 g33521 (by norm_num)
    exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 151 g151 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2099) h  -- d = 2099: 23^2 | 9521+1
    rw [show (2:ℕ) ^ 2099 = (2 ^ 200) ^ 10 * 2 ^ 99 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 99 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g34675481 : 34675481 ∈ P := S2 34675481 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 34675481 (by norm_num))
    have g9521 : 9521 ∈ P := S1 9521 (by norm_num) (by norm_num) (hnz (by norm_num)) 34675481 g34675481 (by norm_num)
    exact S6 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 9521 g9521 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2103) h  -- d = 2103: 7 | 214507+1, 41+1
    rw [show (2:ℕ) ^ 2103 = (2 ^ 200) ^ 10 * 2 ^ 103 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 103 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g214507 : 214507 ∈ P := S2 214507 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 214507 (by norm_num))
    have g163 : 163 ∈ P := S1 163 (by norm_num) (by norm_num) (hnz (by norm_num)) 214507 g214507 (by norm_num)
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 163 g163 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 214507 g214507 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2105) h  -- d = 2105: 11 | 2^2105+1, 307+1
    rw [show (2:ℕ) ^ 2105 = (2 ^ 200) ^ 10 * 2 ^ 105 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 105 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g206291 : 206291 ∈ P := S2 206291 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 206291 (by norm_num))
    have g17191 : 17191 ∈ P := S1 17191 (by norm_num) (by norm_num) (hnz (by norm_num)) 206291 g206291 (by norm_num)
    have g307 : 307 ∈ P := S1 307 (by norm_num) (by norm_num) (hnz (by norm_num)) 17191 g17191 (by norm_num)
    exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11 (by norm_num)) 307 g307 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2129) h  -- d = 2129: 3^6 | (2^2129+1) prod (p+1), p in {4259, 17033, 5, 17}
    rw [show (2:ℕ) ^ 2129 = (2 ^ 200) ^ 10 * 2 ^ 129 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 129 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4259 : 4259 ∈ P := S2 4259 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4259 (by norm_num))
    have g17033 : 17033 ∈ P := S2 17033 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17033 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4259 g4259 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 17033 g17033 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g4259 (by simp) (by norm_num : 3 ^ 1 ∣ 4259 + 1)
    have b2 := bud_cons b1 g17033 (by simp) (by norm_num : 3 ^ 1 ∣ 17033 + 1)
    have b3 := bud_cons b2 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b4 := bud_cons b3 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2153) h  -- d = 2153: 5^2 | 4340449+1
    rw [show (2:ℕ) ^ 2153 = (2 ^ 200) ^ 10 * 2 ^ 153 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 153 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4340449 : 4340449 ∈ P := S2 4340449 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4340449 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4340449 g4340449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2157) h  -- d = 2157: 61 | 3^5+1, 8576233+1
    rw [show (2:ℕ) ^ 2157 = (2 ^ 200) ^ 10 * 2 ^ 157 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 157 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8576233 : 8576233 ∈ P := S2 8576233 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8576233 (by norm_num))
    exact S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 8576233 g8576233 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2177) h  -- d = 2177: 11^2 | 2903+1
    rw [show (2:ℕ) ^ 2177 = (2 ^ 200) ^ 10 * 2 ^ 177 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 177 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17417 : 17417 ∈ P := S2 17417 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17417 (by norm_num))
    have g2903 : 2903 ∈ P := S1 2903 (by norm_num) (by norm_num) (hnz (by norm_num)) 17417 g17417 (by norm_num)
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 2903 g2903 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2191) h  -- d = 2191: 11 | 43+1, 12781+1
    rw [show (2:ℕ) ^ 2191 = (2 ^ 200) ^ 10 * 2 ^ 191 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 191 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 43 (by norm_num))
    have g153371 : 153371 ∈ P := S2 153371 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 153371 (by norm_num))
    have g12781 : 12781 ∈ P := S1 12781 (by norm_num) (by norm_num) (hnz (by norm_num)) 153371 g153371 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 12781 g12781 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2199) h  -- d = 2199: 5 | 1037929+1, 19+1
    rw [show (2:ℕ) ^ 2199 = (2 ^ 200) ^ 10 * 2 ^ 199 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 199 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1037929 : 1037929 ∈ P := S2 1037929 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1037929 (by norm_num))
    have g1350187 : 1350187 ∈ P := S2 1350187 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1350187 (by norm_num))
    have g48221 : 48221 ∈ P := S1 48221 (by norm_num) (by norm_num) (hnz (by norm_num)) 1350187 g1350187 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 48221 g48221 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1037929 g1037929 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2217) h  -- d = 2217: 5^2 | 2699+1
    rw [show (2:ℕ) ^ 2217 = (2 ^ 200) ^ 11 * 2 ^ 17 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 17 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g124153 : 124153 ∈ P := S2 124153 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 124153 (by norm_num))
    have g2699 : 2699 ∈ P := S1 2699 (by norm_num) (by norm_num) (hnz (by norm_num)) 124153 g124153 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2699 g2699 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2221) h  -- d = 2221: 5^2 | 1999+1
    rw [show (2:ℕ) ^ 2221 = (2 ^ 200) ^ 11 * 2 ^ 21 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 21 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g39979 : 39979 ∈ P := S2 39979 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 39979 (by norm_num))
    have g1999 : 1999 ∈ P := S1 1999 (by norm_num) (by norm_num) (hnz (by norm_num)) 39979 g39979 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1999 g1999 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2237) h  -- d = 2237: 3^6 | (2^2237+1) prod (p+1), p in {503, 4643}
    rw [show (2:ℕ) ^ 2237 = (2 ^ 200) ^ 11 * 2 ^ 37 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 37 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4670857 : 4670857 ∈ P := S2 4670857 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4670857 (by norm_num))
    have g503 : 503 ∈ P := S1 503 (by norm_num) (by norm_num) (hnz (by norm_num)) 4670857 g4670857 (by norm_num)
    have g4643 : 4643 ∈ P := S1 4643 (by norm_num) (by norm_num) (hnz (by norm_num)) 4670857 g4670857 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g503 (by simp) (by norm_num : 3 ^ 2 ∣ 503 + 1)
    have b2 := bud_cons b1 g4643 (by simp) (by norm_num : 3 ^ 3 ∣ 4643 + 1)
    exact budget_kernel3 hP h3P E b2.1 ((pow_dvd_pow 3 (by norm_num)).trans b2.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2239) h  -- d = 2239: 5 | 29+1, 109+1
    rw [show (2:ℕ) ^ 2239 = (2 ^ 200) ^ 11 * 2 ^ 39 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 39 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g107473 : 107473 ∈ P := S2 107473 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 107473 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 107473 g107473 (by norm_num)
    have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 107473 g107473 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 109 g109 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2243) h  -- d = 2243: 5^2 | 3445249+1
    rw [show (2:ℕ) ^ 2243 = (2 ^ 200) ^ 11 * 2 ^ 43 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 43 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6890497 : 6890497 ∈ P := S2 6890497 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6890497 (by norm_num))
    have g3445249 : 3445249 ∈ P := S1 3445249 (by norm_num) (by norm_num) (hnz (by norm_num)) 6890497 g6890497 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3445249 g3445249 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2251) h  -- d = 2251: 3^6 | (2^2251+1) prod (p+1), p in {36017, 23, 29}
    rw [show (2:ℕ) ^ 2251 = (2 ^ 200) ^ 11 * 2 ^ 51 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 51 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g36017 : 36017 ∈ P := S2 36017 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 36017 (by norm_num))
    have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 36017 g36017 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 36017 g36017 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g36017 (by simp) (by norm_num : 3 ^ 3 ∣ 36017 + 1)
    have b2 := bud_cons b1 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
    have b3 := bud_cons b2 g29 (by simp) (by norm_num : 3 ^ 1 ∣ 29 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2269) h  -- d = 2269: 5 | 109+1, 19+1
    rw [show (2:ℕ) ^ 2269 = (2 ^ 200) ^ 11 * 2 ^ 69 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 69 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g10659763 : 10659763 ∈ P := S2 10659763 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 10659763 (by norm_num))
    have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 10659763 g10659763 (by norm_num)
    have g1063 : 1063 ∈ P := S1 1063 (by norm_num) (by norm_num) (hnz (by norm_num)) 10659763 g10659763 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 1063 g1063 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 109 g109 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2271) h  -- d = 2271: 5 | 18169+1, 79+1
    rw [show (2:ℕ) ^ 2271 = (2 ^ 200) ^ 11 * 2 ^ 71 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 71 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g18169 : 18169 ∈ P := S2 18169 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 18169 (by norm_num))
    have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 18169 g18169 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 18169 g18169 79 g79 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2273) h  -- d = 2273: 5 | 379+1, 19+1
    rw [show (2:ℕ) ^ 2273 = (2 ^ 200) ^ 11 * 2 ^ 73 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 73 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4547 : 4547 ∈ P := S2 4547 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4547 (by norm_num))
    have g379 : 379 ∈ P := S1 379 (by norm_num) (by norm_num) (hnz (by norm_num)) 4547 g4547 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 379 g379 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 379 g379 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2281) h  -- d = 2281: 31 | 61+1, 557+1
    rw [show (2:ℕ) ^ 2281 = (2 ^ 200) ^ 11 * 2 ^ 81 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 81 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    have g95803 : 95803 ∈ P := S2 95803 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 95803 (by norm_num))
    have g557 : 557 ∈ P := S1 557 (by norm_num) (by norm_num) (hnz (by norm_num)) 95803 g95803 (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 61 g61 557 g557 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2285) h  -- d = 2285: 7 | 41131+1, 13+1
    rw [show (2:ℕ) ^ 2285 = (2 ^ 200) ^ 11 * 2 ^ 85 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 85 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g41131 : 41131 ∈ P := S2 41131 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 41131 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 41131 g41131 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41131 g41131 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2293) h  -- d = 2293: 5 | 12625259+1, 29+1
    rw [show (2:ℕ) ^ 2293 = (2 ^ 200) ^ 11 * 2 ^ 93 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 93 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g12625259 : 12625259 ∈ P := S2 12625259 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 12625259 (by norm_num))
    have g210421 : 210421 ∈ P := S1 210421 (by norm_num) (by norm_num) (hnz (by norm_num)) 12625259 g12625259 (by norm_num)
    have g105211 : 105211 ∈ P := S1 105211 (by norm_num) (by norm_num) (hnz (by norm_num)) 210421 g210421 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 105211 g105211 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 12625259 g12625259 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2307) h  -- d = 2307: 53^2 | 303371+1
    rw [show (2:ℕ) ^ 2307 = (2 ^ 200) ^ 11 * 2 ^ 107 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 107 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1213483 : 1213483 ∈ P := S2 1213483 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1213483 (by norm_num))
    have g303371 : 303371 ∈ P := S1 303371 (by norm_num) (by norm_num) (hnz (by norm_num)) 1213483 g1213483 (by norm_num)
    exact S6 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 303371 g303371 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2333) h  -- d = 2333: 7^2 | 1287817+1
    rw [show (2:ℕ) ^ 2333 = (2 ^ 200) ^ 11 * 2 ^ 133 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 133 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1287817 : 1287817 ∈ P := S2 1287817 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1287817 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1287817 g1287817 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2341) h  -- d = 2341: 7^2 | 3037+1
    rw [show (2:ℕ) ^ 2341 = (2 ^ 200) ^ 11 * 2 ^ 141 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 141 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g224737 : 224737 ∈ P := S2 224737 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 224737 (by norm_num))
    have g3037 : 3037 ∈ P := S1 3037 (by norm_num) (by norm_num) (hnz (by norm_num)) 224737 g224737 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 3037 g3037 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2347) h  -- d = 2347: 7 | 14083+1, 503+1
    rw [show (2:ℕ) ^ 2347 = (2 ^ 200) ^ 11 * 2 ^ 147 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 147 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14083 : 14083 ∈ P := S2 14083 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14083 (by norm_num))
    have g503 : 503 ∈ P := S1 503 (by norm_num) (by norm_num) (hnz (by norm_num)) 14083 g14083 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 14083 g14083 503 g503 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2357) h  -- d = 2357: 5^2 | 23249449+1
    rw [show (2:ℕ) ^ 2357 = (2 ^ 200) ^ 11 * 2 ^ 157 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 157 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g23249449 : 23249449 ∈ P := S2 23249449 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 23249449 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 23249449 g23249449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2383) h  -- d = 2383: 7 | 181+1, 13+1
    rw [show (2:ℕ) ^ 2383 = (2 ^ 200) ^ 11 * 2 ^ 183 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 183 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g57193 : 57193 ∈ P := S2 57193 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 57193 (by norm_num))
    have g28597 : 28597 ∈ P := S1 28597 (by norm_num) (by norm_num) (hnz (by norm_num)) 57193 g57193 (by norm_num)
    have g181 : 181 ∈ P := S1 181 (by norm_num) (by norm_num) (hnz (by norm_num)) 28597 g28597 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2399) h  -- d = 2399: 5 | 3531329+1, 29+1
    rw [show (2:ℕ) ^ 2399 = (2 ^ 200) ^ 11 * 2 ^ 199 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 199 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3531329 : 3531329 ∈ P := S2 3531329 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3531329 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 3531329 g3531329 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3531329 g3531329 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2435) h  -- d = 2435: 11 | 2^2435+1, 769+1
    rw [show (2:ℕ) ^ 2435 = (2 ^ 200) ^ 12 * 2 ^ 35 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 35 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g58441 : 58441 ∈ P := S2 58441 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 58441 (by norm_num))
    have g29221 : 29221 ∈ P := S1 29221 (by norm_num) (by norm_num) (hnz (by norm_num)) 58441 g58441 (by norm_num)
    have g769 : 769 ∈ P := S1 769 (by norm_num) (by norm_num) (hnz (by norm_num)) 29221 g29221 (by norm_num)
    exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11 (by norm_num)) 769 g769 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2441) h  -- d = 2441: 5 | 1191209+1, 59+1
    rw [show (2:ℕ) ^ 2441 = (2 ^ 200) ^ 12 * 2 ^ 41 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 41 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1191209 : 1191209 ∈ P := S2 1191209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1191209 (by norm_num))
    have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 1191209 g1191209 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1191209 g1191209 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2447) h  -- d = 2447: 7 | 13+1, 251+1
    rw [show (2:ℕ) ^ 2447 = (2 ^ 200) ^ 12 * 2 ^ 47 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 47 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g19577 : 19577 ∈ P := S2 19577 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 19577 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 19577 g19577 (by norm_num)
    have g251 : 251 ∈ P := S1 251 (by norm_num) (by norm_num) (hnz (by norm_num)) 19577 g19577 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 251 g251 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2471) h  -- d = 2471: 43 | 2^2471+1, 12824491+1
    rw [show (2:ℕ) ^ 2471 = (2 ^ 200) ^ 12 * 2 ^ 71 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 71 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g12824491 : 12824491 ∈ P := S2 12824491 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 12824491 (by norm_num))
    exact S4 43 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 43 (by norm_num)) 12824491 g12824491 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2477) h  -- d = 2477: 5 | 1789+1, 179+1
    rw [show (2:ℕ) ^ 2477 = (2 ^ 200) ^ 12 * 2 ^ 77 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 77 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g64403 : 64403 ∈ P := S2 64403 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 64403 (by norm_num))
    have g1789 : 1789 ∈ P := S1 1789 (by norm_num) (by norm_num) (hnz (by norm_num)) 64403 g64403 (by norm_num)
    have g179 : 179 ∈ P := S1 179 (by norm_num) (by norm_num) (hnz (by norm_num)) 1789 g1789 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1789 g1789 179 g179 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2503) h  -- d = 2503: 17^2 | 577+1
    rw [show (2:ℕ) ^ 2503 = (2 ^ 200) ^ 12 * 2 ^ 103 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 103 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g33920657 : 33920657 ∈ P := S2 33920657 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 33920657 (by norm_num))
    have g1884481 : 1884481 ∈ P := S1 1884481 (by norm_num) (by norm_num) (hnz (by norm_num)) 33920657 g33920657 (by norm_num)
    have g577 : 577 ∈ P := S1 577 (by norm_num) (by norm_num) (hnz (by norm_num)) 1884481 g1884481 (by norm_num)
    exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 577 g577 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2517) h  -- d = 2517: 5 | 3181489+1, 4079+1
    rw [show (2:ℕ) ^ 2517 = (2 ^ 200) ^ 12 * 2 ^ 117 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 117 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3181489 : 3181489 ∈ P := S2 3181489 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3181489 (by norm_num))
    have g24473 : 24473 ∈ P := S1 24473 (by norm_num) (by norm_num) (hnz (by norm_num)) 3181489 g3181489 (by norm_num)
    have g4079 : 4079 ∈ P := S1 4079 (by norm_num) (by norm_num) (hnz (by norm_num)) 24473 g24473 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3181489 g3181489 4079 g4079 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2543) h  -- d = 2543: 5 | 1464769+1, 79+1
    rw [show (2:ℕ) ^ 2543 = (2 ^ 200) ^ 12 * 2 ^ 143 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 143 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1464769 : 1464769 ∈ P := S2 1464769 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1464769 (by norm_num))
    have g146477 : 146477 ∈ P := S1 146477 (by norm_num) (by norm_num) (hnz (by norm_num)) 1464769 g1464769 (by norm_num)
    have g24413 : 24413 ∈ P := S1 24413 (by norm_num) (by norm_num) (hnz (by norm_num)) 146477 g146477 (by norm_num)
    have g313 : 313 ∈ P := S1 313 (by norm_num) (by norm_num) (hnz (by norm_num)) 24413 g24413 (by norm_num)
    have g157 : 157 ∈ P := S1 157 (by norm_num) (by norm_num) (hnz (by norm_num)) 313 g313 (by norm_num)
    have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 157 g157 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1464769 g1464769 79 g79 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2545) h  -- d = 2545: 3^6 | (2^2545+1) prod (p+1), p in {11, 1019, 5, 17}
    rw [show (2:ℕ) ^ 2545 = (2 ^ 200) ^ 12 * 2 ^ 145 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 145 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g11 : 11 ∈ P := S2 11 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11 (by norm_num))
    have g1019 : 1019 ∈ P := S2 1019 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1019 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1019 g1019 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 1019 g1019 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b2 := bud_cons b1 g1019 (by simp) (by norm_num : 3 ^ 1 ∣ 1019 + 1)
    have b3 := bud_cons b2 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b4 := bud_cons b3 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2549) h  -- d = 2549: 5^2 | 5099+1
    rw [show (2:ℕ) ^ 2549 = (2 ^ 200) ^ 12 * 2 ^ 149 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 149 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5099 : 5099 ∈ P := S2 5099 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5099 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5099 g5099 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2571) h  -- d = 2571: 5^2 | 2749+1
    rw [show (2:ℕ) ^ 2571 = (2 ^ 200) ^ 12 * 2 ^ 171 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 171 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g714739 : 714739 ∈ P := S2 714739 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 714739 (by norm_num))
    have g2749 : 2749 ∈ P := S1 2749 (by norm_num) (by norm_num) (hnz (by norm_num)) 714739 g714739 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2749 g2749 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2579) h  -- d = 2579: 3^6 | (2^2579+1) prod (p+1), p in {14891147, 173, 797}
    rw [show (2:ℕ) ^ 2579 = (2 ^ 200) ^ 12 * 2 ^ 179 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 179 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14891147 : 14891147 ∈ P := S2 14891147 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14891147 (by norm_num))
    have g173 : 173 ∈ P := S1 173 (by norm_num) (by norm_num) (hnz (by norm_num)) 14891147 g14891147 (by norm_num)
    have g797 : 797 ∈ P := S1 797 (by norm_num) (by norm_num) (hnz (by norm_num)) 14891147 g14891147 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g14891147 (by simp) (by norm_num : 3 ^ 3 ∣ 14891147 + 1)
    have b2 := bud_cons b1 g173 (by simp) (by norm_num : 3 ^ 1 ∣ 173 + 1)
    have b3 := bud_cons b2 g797 (by simp) (by norm_num : 3 ^ 1 ∣ 797 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2589) h  -- d = 2589: 5 | 5179+1, 19+1
    rw [show (2:ℕ) ^ 2589 = (2 ^ 200) ^ 12 * 2 ^ 189 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 189 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5179 : 5179 ∈ P := S2 5179 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5179 (by norm_num))
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 5179 g5179 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5179 g5179 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2593) h  -- d = 2593: 3^6 | (2^2593+1) prod (p+1), p in {2063, 5, 107}
    rw [show (2:ℕ) ^ 2593 = (2 ^ 200) ^ 12 * 2 ^ 193 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 193 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8821387 : 8821387 ∈ P := S2 8821387 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8821387 (by norm_num))
    have g2063 : 2063 ∈ P := S1 2063 (by norm_num) (by norm_num) (hnz (by norm_num)) 8821387 g8821387 (by norm_num)
    have g1069 : 1069 ∈ P := S1 1069 (by norm_num) (by norm_num) (hnz (by norm_num)) 8821387 g8821387 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1069 g1069 (by norm_num)
    have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (hnz (by norm_num)) 1069 g1069 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g2063 (by simp) (by norm_num : 3 ^ 1 ∣ 2063 + 1)
    have b2 := bud_cons b1 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b3 := bud_cons b2 g107 (by simp) (by norm_num : 3 ^ 3 ∣ 107 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2609) h  -- d = 2609: 7^2 | 20873+1
    rw [show (2:ℕ) ^ 2609 = (2 ^ 200) ^ 13 * 2 ^ 9 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 9 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g20873 : 20873 ∈ P := S2 20873 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 20873 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 20873 g20873 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2611) h  -- d = 2611: 3^6 | (2^2611+1) prod (p+1), p in {11, 15107, 1259, 5}
    rw [show (2:ℕ) ^ 2611 = (2 ^ 200) ^ 13 * 2 ^ 11 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 11 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 43 (by norm_num))
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
    have g60427 : 60427 ∈ P := S2 60427 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 60427 (by norm_num))
    have g15107 : 15107 ∈ P := S1 15107 (by norm_num) (by norm_num) (hnz (by norm_num)) 60427 g60427 (by norm_num)
    have g1259 : 1259 ∈ P := S1 1259 (by norm_num) (by norm_num) (hnz (by norm_num)) 15107 g15107 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1259 g1259 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b2 := bud_cons b1 g15107 (by simp) (by norm_num : 3 ^ 1 ∣ 15107 + 1)
    have b3 := bud_cons b2 g1259 (by simp) (by norm_num : 3 ^ 2 ∣ 1259 + 1)
    have b4 := bud_cons b3 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2631) h  -- d = 2631: 3^6 | (2^2631+1) prod (p+1), p in {29819, 5, 71}
    rw [show (2:ℕ) ^ 2631 = (2 ^ 200) ^ 13 * 2 ^ 31 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 31 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g29819 : 29819 ∈ P := S2 29819 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 29819 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29819 g29819 (by norm_num)
    have g71 : 71 ∈ P := S1 71 (by norm_num) (by norm_num) (hnz (by norm_num)) 29819 g29819 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 2 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 2) (by norm_num))⟩
    have b1 := bud_cons b0 g29819 (by simp) (by norm_num : 3 ^ 1 ∣ 29819 + 1)
    have b2 := bud_cons b1 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b3 := bud_cons b2 g71 (by simp) (by norm_num : 3 ^ 2 ∣ 71 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2647) h  -- d = 2647: 5 | 8110409+1, 439+1
    rw [show (2:ℕ) ^ 2647 = (2 ^ 200) ^ 13 * 2 ^ 47 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 47 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8110409 : 8110409 ∈ P := S2 8110409 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8110409 (by norm_num))
    have g3511 : 3511 ∈ P := S1 3511 (by norm_num) (by norm_num) (hnz (by norm_num)) 8110409 g8110409 (by norm_num)
    have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 3511 g3511 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 8110409 g8110409 439 g439 (by norm_num) (by norm_num)) (by norm_num)

set_option maxHeartbeats 17200000 in
theorem odd_4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d ∈ ({2689, 2693, 2699, 2707, 2711, 2719, 2721, 2733, 2741, 2753, 2817, 2819, 2837, 2851, 2863, 2903,
      2927, 2939, 2947, 2949, 2953, 2957, 2959, 2965, 2969, 2981, 2999, 3005, 3037, 3061, 3065,
      3067, 3089, 3093, 3117, 3121, 3137, 3167} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2689) h  -- d = 2689: 7^2 | 523907+1
    rw [show (2:ℕ) ^ 2689 = (2 ^ 200) ^ 13 * 2 ^ 89 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 89 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6286883 : 6286883 ∈ P := S2 6286883 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6286883 (by norm_num))
    have g523907 : 523907 ∈ P := S1 523907 (by norm_num) (by norm_num) (hnz (by norm_num)) 6286883 g6286883 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 523907 g523907 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2693) h  -- d = 2693: 5^2 | 449+1
    rw [show (2:ℕ) ^ 2693 = (2 ^ 200) ^ 13 * 2 ^ 93 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 93 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5387 : 5387 ∈ P := S2 5387 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5387 (by norm_num))
    have g449 : 449 ∈ P := S1 449 (by norm_num) (by norm_num) (hnz (by norm_num)) 5387 g5387 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 449 g449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2699) h  -- d = 2699: 5 | 1039+1, 19+1
    rw [show (2:ℕ) ^ 2699 = (2 ^ 200) ^ 13 * 2 ^ 99 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 99 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g469627 : 469627 ∈ P := S2 469627 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 469627 (by norm_num))
    have g1039 : 1039 ∈ P := S1 1039 (by norm_num) (by norm_num) (hnz (by norm_num)) 469627 g469627 (by norm_num)
    have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 469627 g469627 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 113 g113 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1039 g1039 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2707) h  -- d = 2707: 19^2 | 7219+1
    rw [show (2:ℕ) ^ 2707 = (2 ^ 200) ^ 13 * 2 ^ 107 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 107 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g43313 : 43313 ∈ P := S2 43313 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 43313 (by norm_num))
    have g7219 : 7219 ∈ P := S1 7219 (by norm_num) (by norm_num) (hnz (by norm_num)) 43313 g43313 (by norm_num)
    exact S6 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 7219 g7219 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2711) h  -- d = 2711: 7^2 | 16267+1
    rw [show (2:ℕ) ^ 2711 = (2 ^ 200) ^ 13 * 2 ^ 111 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 111 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g16267 : 16267 ∈ P := S2 16267 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16267 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 16267 g16267 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2719) h  -- d = 2719: 7^2 | 97+1
    rw [show (2:ℕ) ^ 2719 = (2 ^ 200) ^ 13 * 2 ^ 119 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 119 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g174017 : 174017 ∈ P := S2 174017 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 174017 (by norm_num))
    have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 174017 g174017 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2721) h  -- d = 2721: 3^8 | (2^2721+1) prod (p+1), p in {1361, 6803}
    rw [show (2:ℕ) ^ 2721 = (2 ^ 200) ^ 13 * 2 ^ 121 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 121 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5443 : 5443 ∈ P := S2 5443 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5443 (by norm_num))
    have g1361 : 1361 ∈ P := S1 1361 (by norm_num) (by norm_num) (hnz (by norm_num)) 5443 g5443 (by norm_num)
    have g27211 : 27211 ∈ P := S2 27211 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 27211 (by norm_num))
    have g6803 : 6803 ∈ P := S1 6803 (by norm_num) (by norm_num) (hnz (by norm_num)) 27211 g27211 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 2 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 2) (by norm_num))⟩
    have b1 := bud_cons b0 g1361 (by simp) (by norm_num : 3 ^ 1 ∣ 1361 + 1)
    have b2 := bud_cons b1 g6803 (by simp) (by norm_num : 3 ^ 5 ∣ 6803 + 1)
    exact budget_kernel3 hP h3P E b2.1 ((pow_dvd_pow 3 (by norm_num)).trans b2.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2733) h  -- d = 2733: 7 | 17496667+1, 41+1
    rw [show (2:ℕ) ^ 2733 = (2 ^ 200) ^ 13 * 2 ^ 133 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 133 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17496667 : 17496667 ∈ P := S2 17496667 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17496667 (by norm_num))
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 17496667 g17496667 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 17496667 g17496667 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2741) h  -- d = 2741: 5 | 49339+1, 229+1
    rw [show (2:ℕ) ^ 2741 = (2 ^ 200) ^ 13 * 2 ^ 141 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 141 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g49339 : 49339 ∈ P := S2 49339 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 49339 (by norm_num))
    have g5483 : 5483 ∈ P := S2 5483 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5483 (by norm_num))
    have g457 : 457 ∈ P := S1 457 (by norm_num) (by norm_num) (hnz (by norm_num)) 5483 g5483 (by norm_num)
    have g229 : 229 ∈ P := S1 229 (by norm_num) (by norm_num) (hnz (by norm_num)) 457 g457 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 49339 g49339 229 g229 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2753) h  -- d = 2753: 11 | 947033+1, 7660223+1
    rw [show (2:ℕ) ^ 2753 = (2 ^ 200) ^ 13 * 2 ^ 153 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 153 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g947033 : 947033 ∈ P := S2 947033 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 947033 (by norm_num))
    have g30640891 : 30640891 ∈ P := S2 30640891 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 30640891 (by norm_num))
    have g7660223 : 7660223 ∈ P := S1 7660223 (by norm_num) (by norm_num) (hnz (by norm_num)) 30640891 g30640891 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 947033 g947033 7660223 g7660223 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2817) h  -- d = 2817: 11^2 | 180289+1
    rw [show (2:ℕ) ^ 2817 = (2 ^ 200) ^ 14 * 2 ^ 17 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 17 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g180289 : 180289 ∈ P := S2 180289 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 180289 (by norm_num))
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 180289 g180289 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2819) h  -- d = 2819: 5 | 2542739+1, 42379+1
    rw [show (2:ℕ) ^ 2819 = (2 ^ 200) ^ 14 * 2 ^ 19 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 19 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2542739 : 2542739 ∈ P := S2 2542739 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2542739 (by norm_num))
    have g42379 : 42379 ∈ P := S1 42379 (by norm_num) (by norm_num) (hnz (by norm_num)) 2542739 g2542739 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2542739 g2542739 42379 g42379 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2837) h  -- d = 2837: 3^6 | (2^2837+1) prod (p+1), p in {2269601, 17, 5}
    rw [show (2:ℕ) ^ 2837 = (2 ^ 200) ^ 14 * 2 ^ 37 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 37 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2269601 : 2269601 ∈ P := S2 2269601 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2269601 (by norm_num))
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 2269601 g2269601 (by norm_num)
    have g7417 : 7417 ∈ P := S1 7417 (by norm_num) (by norm_num) (hnz (by norm_num)) 2269601 g2269601 (by norm_num)
    have g3709 : 3709 ∈ P := S1 3709 (by norm_num) (by norm_num) (hnz (by norm_num)) 7417 g7417 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3709 g3709 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g2269601 (by simp) (by norm_num : 3 ^ 2 ∣ 2269601 + 1)
    have b2 := bud_cons b1 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b3 := bud_cons b2 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2851) h  -- d = 2851: 7 | 17107+1, 13+1
    rw [show (2:ℕ) ^ 2851 = (2 ^ 200) ^ 14 * 2 ^ 51 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 51 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17107 : 17107 ∈ P := S2 17107 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17107 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 17107 g17107 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 17107 g17107 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2863) h  -- d = 2863: 11 | 43+1, 7535417+1
    rw [show (2:ℕ) ^ 2863 = (2 ^ 200) ^ 14 * 2 ^ 63 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 63 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 43 (by norm_num))
    have g7535417 : 7535417 ∈ P := S2 7535417 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7535417 (by norm_num))
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 7535417 g7535417 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2903) h  -- d = 2903: 5 | 17419+1, 365779+1
    rw [show (2:ℕ) ^ 2903 = (2 ^ 200) ^ 14 * 2 ^ 103 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 103 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17419 : 17419 ∈ P := S2 17419 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17419 (by norm_num))
    have g365779 : 365779 ∈ P := S2 365779 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 365779 (by norm_num))
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 17419 g17419 365779 g365779 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2927) h  -- d = 2927: 31 | 61+1, 1301+1
    rw [show (2:ℕ) ^ 2927 = (2 ^ 200) ^ 14 * 2 ^ 127 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 127 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    have g23417 : 23417 ∈ P := S2 23417 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 23417 (by norm_num))
    have g1301 : 1301 ∈ P := S1 1301 (by norm_num) (by norm_num) (hnz (by norm_num)) 23417 g23417 (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 61 g61 1301 g1301 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2939) h  -- d = 2939: 5^2 | 94049+1
    rw [show (2:ℕ) ^ 2939 = (2 ^ 200) ^ 14 * 2 ^ 139 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 139 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g94049 : 94049 ∈ P := S2 94049 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 94049 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 94049 g94049 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2947) h  -- d = 2947: 11 | 43+1, 4421+1
    rw [show (2:ℕ) ^ 2947 = (2 ^ 200) ^ 14 * 2 ^ 147 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 147 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 43 (by norm_num))
    have g17683 : 17683 ∈ P := S2 17683 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17683 (by norm_num))
    have g4421 : 4421 ∈ P := S1 4421 (by norm_num) (by norm_num) (hnz (by norm_num)) 17683 g17683 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 4421 g4421 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2949) h  -- d = 2949: 3^6 | (2^2949+1) prod (p+1), p in {83, 8243, 5}
    rw [show (2:ℕ) ^ 2949 = (2 ^ 200) ^ 14 * 2 ^ 149 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 149 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1368337 : 1368337 ∈ P := S2 1368337 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1368337 (by norm_num))
    have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 1368337 g1368337 (by norm_num)
    have g8243 : 8243 ∈ P := S1 8243 (by norm_num) (by norm_num) (hnz (by norm_num)) 1368337 g1368337 (by norm_num)
    have g229 : 229 ∈ P := S1 229 (by norm_num) (by norm_num) (hnz (by norm_num)) 8243 g8243 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 229 g229 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 2 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 2) (by norm_num))⟩
    have b1 := bud_cons b0 g83 (by simp) (by norm_num : 3 ^ 1 ∣ 83 + 1)
    have b2 := bud_cons b1 g8243 (by simp) (by norm_num : 3 ^ 2 ∣ 8243 + 1)
    have b3 := bud_cons b2 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2953) h  -- d = 2953: 61 | 3^5+1, 117119+1
    rw [show (2:ℕ) ^ 2953 = (2 ^ 200) ^ 14 * 2 ^ 153 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 153 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13820041 : 13820041 ∈ P := S2 13820041 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13820041 (by norm_num))
    have g117119 : 117119 ∈ P := S1 117119 (by norm_num) (by norm_num) (hnz (by norm_num)) 13820041 g13820041 (by norm_num)
    exact S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 117119 g117119 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2957) h  -- d = 2957: 5 | 70969+1, 19+1
    rw [show (2:ℕ) ^ 2957 = (2 ^ 200) ^ 14 * 2 ^ 157 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 157 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g70969 : 70969 ∈ P := S2 70969 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 70969 (by norm_num))
    have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 70969 g70969 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 g151 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 70969 g70969 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2959) h  -- d = 2959: 31 | 615473+1, 61+1
    rw [show (2:ℕ) ^ 2959 = (2 ^ 200) ^ 14 * 2 ^ 159 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 159 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g615473 : 615473 ∈ P := S2 615473 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 615473 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 615473 g615473 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2965) h  -- d = 2965: 11 | 2^2965+1, 1187+1
    rw [show (2:ℕ) ^ 2965 = (2 ^ 200) ^ 14 * 2 ^ 165 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 165 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1187 : 1187 ∈ P := S2 1187 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1187 (by norm_num))
    exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11 (by norm_num)) 1187 g1187 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2969) h  -- d = 2969: 3^6 | (2^2969+1) prod (p+1), p in {5939, 5, 11}
    rw [show (2:ℕ) ^ 2969 = (2 ^ 200) ^ 14 * 2 ^ 169 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 169 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5939 : 5939 ∈ P := S2 5939 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5939 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5939 g5939 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 5939 g5939 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 1) (by norm_num))⟩
    have b1 := bud_cons b0 g5939 (by simp) (by norm_num : 3 ^ 3 ∣ 5939 + 1)
    have b2 := bud_cons b1 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b3 := bud_cons b2 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2981) h  -- d = 2981: 19 | 683+1, 37+1
    rw [show (2:ℕ) ^ 2981 = (2 ^ 200) ^ 14 * 2 ^ 181 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 181 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g683 : 683 ∈ P := S2 683 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 683 (by norm_num))
    have g1627 : 1627 ∈ P := S2 1627 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1627 (by norm_num))
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 1627 g1627 (by norm_num)
    exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 683 g683 37 g37 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2999) h  -- d = 2999: 31 | 23993+1, 61+1
    rw [show (2:ℕ) ^ 2999 = (2 ^ 200) ^ 14 * 2 ^ 199 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 199 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g23993 : 23993 ∈ P := S2 23993 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 23993 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 23993 g23993 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3005) h  -- d = 3005: 7 | 167+1, 144241+1
    rw [show (2:ℕ) ^ 3005 = (2 ^ 200) ^ 15 * 2 ^ 5 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 5 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6011 : 6011 ∈ P := S2 6011 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6011 (by norm_num))
    have g167 : 167 ∈ P := S1 167 (by norm_num) (by norm_num) (hnz (by norm_num)) 6011 g6011 (by norm_num)
    have g288481 : 288481 ∈ P := S2 288481 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 288481 (by norm_num))
    have g144241 : 144241 ∈ P := S1 144241 (by norm_num) (by norm_num) (hnz (by norm_num)) 288481 g288481 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 167 g167 144241 g144241 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3037) h  -- d = 3037: 5^2 | 4112099+1
    rw [show (2:ℕ) ^ 3037 = (2 ^ 200) ^ 15 * 2 ^ 37 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 37 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4112099 : 4112099 ∈ P := S2 4112099 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4112099 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4112099 g4112099 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3061) h  -- d = 3061: 7 | 275491+1, 41+1
    rw [show (2:ℕ) ^ 3061 = (2 ^ 200) ^ 15 * 2 ^ 61 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 61 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g275491 : 275491 ∈ P := S2 275491 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 275491 (by norm_num))
    have g9839 : 9839 ∈ P := S1 9839 (by norm_num) (by norm_num) (hnz (by norm_num)) 275491 g275491 (by norm_num)
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 9839 g9839 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 275491 g275491 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3065) h  -- d = 3065: 5 | 29+1, 229+1
    rw [show (2:ℕ) ^ 3065 = (2 ^ 200) ^ 15 * 2 ^ 65 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 65 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g79691 : 79691 ∈ P := S2 79691 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 79691 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 79691 g79691 (by norm_num)
    have g229 : 229 ∈ P := S1 229 (by norm_num) (by norm_num) (hnz (by norm_num)) 79691 g79691 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 229 g229 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3067) h  -- d = 3067: 31 | 21395393+1, 61+1
    rw [show (2:ℕ) ^ 3067 = (2 ^ 200) ^ 15 * 2 ^ 67 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 67 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g21395393 : 21395393 ∈ P := S2 21395393 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 21395393 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 21395393 g21395393 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3089) h  -- d = 3089: 5^2 | 199+1
    rw [show (2:ℕ) ^ 3089 = (2 ^ 200) ^ 15 * 2 ^ 89 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 89 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2001673 : 2001673 ∈ P := S2 2001673 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2001673 (by norm_num))
    have g397 : 397 ∈ P := S1 397 (by norm_num) (by norm_num) (hnz (by norm_num)) 2001673 g2001673 (by norm_num)
    have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 397 g397 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3093) h  -- d = 3093: 3^7 | (2^3093+1) prod (p+1), p in {2447, 5, 17}
    rw [show (2:ℕ) ^ 3093 = (2 ^ 200) ^ 15 * 2 ^ 93 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 93 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g773251 : 773251 ∈ P := S2 773251 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 773251 (by norm_num))
    have g2447 : 2447 ∈ P := S1 2447 (by norm_num) (by norm_num) (hnz (by norm_num)) 773251 g773251 (by norm_num)
    have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 773251 g773251 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 79 g79 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 2447 g2447 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 2 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 2) (by norm_num))⟩
    have b1 := bud_cons b0 g2447 (by simp) (by norm_num : 3 ^ 2 ∣ 2447 + 1)
    have b2 := bud_cons b1 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b3 := bud_cons b2 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3117) h  -- d = 3117: 5^2 | 19949+1
    rw [show (2:ℕ) ^ 3117 = (2 ^ 200) ^ 15 * 2 ^ 117 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 117 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g398977 : 398977 ∈ P := S2 398977 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 398977 (by norm_num))
    have g199489 : 199489 ∈ P := S1 199489 (by norm_num) (by norm_num) (hnz (by norm_num)) 398977 g398977 (by norm_num)
    have g19949 : 19949 ∈ P := S1 19949 (by norm_num) (by norm_num) (hnz (by norm_num)) 199489 g199489 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19949 g19949 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3121) h  -- d = 3121: 53^2 | 56179+1
    rw [show (2:ℕ) ^ 3121 = (2 ^ 200) ^ 15 * 2 ^ 121 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 121 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g56179 : 56179 ∈ P := S2 56179 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 56179 (by norm_num))
    exact S6 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 56179 g56179 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3137) h  -- d = 3137: 13^2 | 6421+1
    rw [show (2:ℕ) ^ 3137 = (2 ^ 200) ^ 15 * 2 ^ 137 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 137 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g26582939 : 26582939 ∈ P := S2 26582939 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 26582939 (by norm_num))
    have g6421 : 6421 ∈ P := S1 6421 (by norm_num) (by norm_num) (hnz (by norm_num)) 26582939 g26582939 (by norm_num)
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 6421 g6421 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3167) h  -- d = 3167: 5 | 1596169+1, 719+1
    rw [show (2:ℕ) ^ 3167 = (2 ^ 200) ^ 15 * 2 ^ 167 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 167 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1596169 : 1596169 ∈ P := S2 1596169 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1596169 (by norm_num))
    have g159617 : 159617 ∈ P := S1 159617 (by norm_num) (by norm_num) (hnz (by norm_num)) 1596169 g1596169 (by norm_num)
    have g719 : 719 ∈ P := S1 719 (by norm_num) (by norm_num) (hnz (by norm_num)) 159617 g159617 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1596169 g1596169 719 g719 (by norm_num) (by norm_num)) (by norm_num)

theorem sieve_odd {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d ∈ (({263, 277, 281, 283, 293, 307, 317, 331, 337, 349, 359, 367, 379, 389, 397, 401, 431, 433, 439,
      443, 449, 461, 467, 479, 499, 521, 523, 541, 547, 557, 569, 571, 577, 587, 599, 607, 631,
      641, 647, 659, 661, 677, 683, 709, 727, 743, 751, 787, 797, 807} : Finset ℕ) ∪
      ({809, 813, 821, 823, 853, 859, 881, 883, 887, 919, 929, 933, 937, 941, 947, 953, 967, 971, 977,
      991, 997, 1009, 1013, 1021, 1041, 1049, 1093, 1097, 1119, 1151, 1153, 1171, 1181, 1193,
      1223, 1227, 1237, 1249, 1257, 1263, 1277, 1279, 1283, 1289, 1291, 1307, 1319, 1327, 1345,
      1355} : Finset ℕ) ∪
      ({1361, 1367, 1399, 1427, 1439, 1451, 1461, 1481, 1483, 1487, 1493, 1499, 1509, 1527, 1531, 1555,
      1559, 1565, 1567, 1571, 1579, 1601, 1609, 1613, 1621, 1627, 1699, 1721, 1733, 1735, 1759,
      1765, 1779, 1789, 1803, 1823, 1839, 1857, 1865, 1871, 1897, 1901, 1915, 1933, 1949, 1973,
      1979, 2017, 2027, 2029} : Finset ℕ) ∪
      ({2045, 2069, 2081, 2095, 2099, 2103, 2105, 2129, 2153, 2157, 2177, 2191, 2199, 2217, 2221, 2237,
      2239, 2243, 2251, 2269, 2271, 2273, 2281, 2285, 2293, 2307, 2333, 2341, 2347, 2357, 2383,
      2399, 2435, 2441, 2447, 2471, 2477, 2503, 2517, 2543, 2545, 2549, 2571, 2579, 2589, 2593,
      2609, 2611, 2631, 2647} : Finset ℕ) ∪
      ({2689, 2693, 2699, 2707, 2711, 2719, 2721, 2733, 2741, 2753, 2817, 2819, 2837, 2851, 2863, 2903,
      2927, 2939, 2947, 2949, 2953, 2957, 2959, 2965, 2969, 2981, 2999, 3005, 3037, 3061, 3065,
      3067, 3089, 3093, 3117, 3121, 3137, 3167} : Finset ℕ)),
      m % (2 * d) ≠ d := by
  intro d hd
  simp only [Finset.mem_union] at hd
  rcases hd with (((h | h) | h) | h) | h
  · exact odd_0 hP h3P E d h
  · exact odd_1 hP h3P E d h
  · exact odd_2 hP h3P E d h
  · exact odd_3 hP h3P E d h
  · exact odd_4 hP h3P E d h

set_option maxHeartbeats 22000000 in
theorem even_0 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d ∈ ({262, 268, 274, 278, 284, 296, 298, 302, 314, 316, 326, 328, 334, 344, 346, 358, 362, 376, 382,
      386, 388, 394, 398, 412, 422, 428, 436, 446, 452, 454, 458, 466, 478, 482, 502, 508, 514,
      526, 536, 538, 542, 548, 554, 562, 568, 586, 604, 614, 622, 626} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 262) h  -- d = 262: 5^2 | 2140199+1
    rw [show (2:ℕ) ^ 262 = (2 ^ 200) ^ 1 * 2 ^ 62 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 62 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g269665073 : 269665073 ∈ P := S2 269665073 prime_269665073 (by norm_num) (hnz (by norm_num)) (R 269665073 (by norm_num))
    have g2140199 : 2140199 ∈ P := S1 2140199 (by norm_num) (by norm_num) (hnz (by norm_num)) 269665073 g269665073 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2140199 g2140199 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 268) h  -- d = 268: 5 | 379+1, 19+1
    rw [show (2:ℕ) ^ 268 = (2 ^ 200) ^ 1 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g75041 : 75041 ∈ P := S2 75041 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 75041 (by norm_num))
    have g379 : 379 ∈ P := S1 379 (by norm_num) (by norm_num) (hnz (by norm_num)) 75041 g75041 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 379 g379 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 379 g379 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 274) h  -- d = 274: 3^6 | (2^274+1) prod (p+1), p in {5, 23633, 101, 17}
    rw [show (2:ℕ) ^ 274 = (2 ^ 200) ^ 1 * 2 ^ 74 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 74 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5 : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num))
    have g189061 : 189061 ∈ P := S2 189061 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 189061 (by norm_num))
    have g94531 : 94531 ∈ P := S1 94531 (by norm_num) (by norm_num) (hnz (by norm_num)) 189061 g189061 (by norm_num)
    have g23633 : 23633 ∈ P := S1 23633 (by norm_num) (by norm_num) (hnz (by norm_num)) 94531 g94531 (by norm_num)
    have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 23633 g23633 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 101 g101 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b2 := bud_cons b1 g23633 (by simp) (by norm_num : 3 ^ 2 ∣ 23633 + 1)
    have b3 := bud_cons b2 g101 (by simp) (by norm_num : 3 ^ 1 ∣ 101 + 1)
    have b4 := bud_cons b3 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 278) h  -- d = 278: 5^2 | 1408349+1
    rw [show (2:ℕ) ^ 278 = (2 ^ 200) ^ 1 * 2 ^ 78 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 78 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1408349 : 1408349 ∈ P := S2 1408349 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1408349 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1408349 g1408349 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 284) h  -- d = 284: 5 | 379+1, 19+1
    rw [show (2:ℕ) ^ 284 = (2 ^ 200) ^ 1 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2273 : 2273 ∈ P := S2 2273 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2273 (by norm_num))
    have g379 : 379 ∈ P := S1 379 (by norm_num) (by norm_num) (hnz (by norm_num)) 2273 g2273 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 379 g379 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 379 g379 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 296) h  -- d = 296: 3^7 | (2^296+1) prod (p+1), p in {257, 80513, 71}
    rw [show (2:ℕ) ^ 296 = (2 ^ 200) ^ 1 * 2 ^ 96 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 96 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g80513 : 80513 ∈ P := S2 80513 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 80513 (by norm_num))
    have g71 : 71 ∈ P := S1 71 (by norm_num) (by norm_num) (hnz (by norm_num)) 80513 g80513 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g80513 (by simp) (by norm_num : 3 ^ 4 ∣ 80513 + 1)
    have b3 := bud_cons b2 g71 (by simp) (by norm_num : 3 ^ 2 ∣ 71 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 298) h  -- d = 298: 5 | 2^298+1, 1789+1
    rw [show (2:ℕ) ^ 298 = (2 ^ 200) ^ 1 * 2 ^ 98 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 98 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1789 : 1789 ∈ P := S2 1789 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1789 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1789 g1789 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 302) h  -- d = 302: 5 | 2^302+1, 19+1
    rw [show (2:ℕ) ^ 302 = (2 ^ 200) ^ 1 * 2 ^ 102 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 102 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2854495385411919762116496381035264358442074113 : 2854495385411919762116496381035264358442074113 ∈ P := S2 2854495385411919762116496381035264358442074113 prime_2854495385411919762116496381035264358442074113 (by norm_num) (hnz (by norm_num)) (R 2854495385411919762116496381035264358442074113 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 2854495385411919762116496381035264358442074113 g2854495385411919762116496381035264358442074113 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 314) h  -- d = 314: 5 | 2^314+1, 256469+1
    rw [show (2:ℕ) ^ 314 = (2 ^ 200) ^ 1 * 2 ^ 114 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 114 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2203942033439148343973 : 2203942033439148343973 ∈ P := S2 2203942033439148343973 prime_2203942033439148343973 (by norm_num) (hnz (by norm_num)) (R 2203942033439148343973 (by norm_num))
    have g256469 : 256469 ∈ P := S1 256469 (by norm_num) (by norm_num) (hnz (by norm_num)) 2203942033439148343973 g2203942033439148343973 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 256469 g256469 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 316) h  -- d = 316: 5 | 994769+1, 1579+1
    rw [show (2:ℕ) ^ 316 = (2 ^ 200) ^ 1 * 2 ^ 116 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 116 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g994769 : 994769 ∈ P := S2 994769 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 994769 (by norm_num))
    have g1579 : 1579 ∈ P := S1 1579 (by norm_num) (by norm_num) (hnz (by norm_num)) 994769 g994769 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 994769 g994769 1579 g1579 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 326) h  -- d = 326: 5^2 | 7807049+1
    rw [show (2:ℕ) ^ 326 = (2 ^ 200) ^ 1 * 2 ^ 126 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 126 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7807049 : 7807049 ∈ P := S2 7807049 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7807049 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 7807049 g7807049 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 328) h  -- d = 328: 5 | 59+1, 27259+1
    rw [show (2:ℕ) ^ 328 = (2 ^ 200) ^ 1 * 2 ^ 128 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 128 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g12239719573537 : 12239719573537 ∈ P := S2 12239719573537 prime_12239719573537 (by norm_num) (hnz (by norm_num)) (R 12239719573537 (by norm_num))
    have g260541521 : 260541521 ∈ P := S1 260541521 prime_260541521 (by norm_num) (hnz (by norm_num)) 12239719573537 g12239719573537 (by norm_num)
    have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 260541521 g260541521 (by norm_num)
    have g27259 : 27259 ∈ P := S1 27259 (by norm_num) (by norm_num) (hnz (by norm_num)) 260541521 g260541521 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 59 g59 27259 g27259 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 334) h  -- d = 334: 5 | 2^334+1, 719+1
    rw [show (2:ℕ) ^ 334 = (2 ^ 200) ^ 1 * 2 ^ 134 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 134 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g75005713 : 75005713 ∈ P := S2 75005713 prime_75005713 (by norm_num) (hnz (by norm_num)) (R 75005713 (by norm_num))
    have g232937 : 232937 ∈ P := S1 232937 (by norm_num) (by norm_num) (hnz (by norm_num)) 75005713 g75005713 (by norm_num)
    have g12941 : 12941 ∈ P := S1 12941 (by norm_num) (by norm_num) (hnz (by norm_num)) 232937 g232937 (by norm_num)
    have g719 : 719 ∈ P := S1 719 (by norm_num) (by norm_num) (hnz (by norm_num)) 12941 g12941 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 719 g719 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 344) h  -- d = 344: 5 | 4129+1, 59+1
    rw [show (2:ℕ) ^ 344 = (2 ^ 200) ^ 1 * 2 ^ 144 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 144 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4129 : 4129 ∈ P := S2 4129 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4129 (by norm_num))
    have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 4129 g4129 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4129 g4129 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 346) h  -- d = 346: 5 | 2^346+1, 19+1
    rw [show (2:ℕ) ^ 346 = (2 ^ 200) ^ 1 * 2 ^ 146 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 146 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7152893721041 : 7152893721041 ∈ P := S2 7152893721041 prime_7152893721041 (by norm_num) (hnz (by norm_num)) (R 7152893721041 (by norm_num))
    have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 7152893721041 g7152893721041 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 113 g113 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 358) h  -- d = 358: 5 | 2^358+1, 19+1
    rw [show (2:ℕ) ^ 358 = (2 ^ 200) ^ 1 * 2 ^ 158 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 158 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g31815461 : 31815461 ∈ P := S2 31815461 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 31815461 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 31815461 g31815461 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 362) h  -- d = 362: 5 | 2^362+1, 52609+1
    rw [show (2:ℕ) ^ 362 = (2 ^ 200) ^ 1 * 2 ^ 162 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 162 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3830538323149121 : 3830538323149121 ∈ P := S2 3830538323149121 prime_3830538323149121 (by norm_num) (hnz (by norm_num)) (R 3830538323149121 (by norm_num))
    have g52609 : 52609 ∈ P := S1 52609 (by norm_num) (by norm_num) (hnz (by norm_num)) 3830538323149121 g3830538323149121 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 52609 g52609 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 376) h  -- d = 376: 5^2 | 3853249+1
    rw [show (2:ℕ) ^ 376 = (2 ^ 200) ^ 1 * 2 ^ 176 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 176 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3853249 : 3853249 ∈ P := S2 3853249 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3853249 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3853249 g3853249 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 382) h  -- d = 382: 7^2 | 3821+1
    rw [show (2:ℕ) ^ 382 = (2 ^ 200) ^ 1 * 2 ^ 182 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 182 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3821 : 3821 ∈ P := S2 3821 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3821 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 3821 g3821 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 386) h  -- d = 386: 5 | 2^386+1, 3089+1
    rw [show (2:ℕ) ^ 386 = (2 ^ 200) ^ 1 * 2 ^ 186 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 186 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3089 : 3089 ∈ P := S2 3089 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3089 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 3089 g3089 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 388) h  -- d = 388: 3^7 | (2^388+1) prod (p+1), p in {17, 25507121, 251, 16937}
    rw [show (2:ℕ) ^ 388 = (2 ^ 200) ^ 1 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g25507121 : 25507121 ∈ P := S2 25507121 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 25507121 (by norm_num))
    have g251 : 251 ∈ P := S1 251 (by norm_num) (by norm_num) (hnz (by norm_num)) 25507121 g25507121 (by norm_num)
    have g16937 : 16937 ∈ P := S1 16937 (by norm_num) (by norm_num) (hnz (by norm_num)) 25507121 g25507121 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g25507121 (by simp) (by norm_num : 3 ^ 1 ∣ 25507121 + 1)
    have b3 := bud_cons b2 g251 (by simp) (by norm_num : 3 ^ 2 ∣ 251 + 1)
    have b4 := bud_cons b3 g16937 (by simp) (by norm_num : 3 ^ 2 ∣ 16937 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 394) h  -- d = 394: 5 | 2^394+1, 4729+1
    rw [show (2:ℕ) ^ 394 = (2 ^ 200) ^ 1 * 2 ^ 194 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 194 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4729 : 4729 ∈ P := S2 4729 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4729 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 4729 g4729 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 398) h  -- d = 398: 5 | 2^398+1, 19+1
    rw [show (2:ℕ) ^ 398 = (2 ^ 200) ^ 1 * 2 ^ 198 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 1 * 2 ^ 198 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g797 : 797 ∈ P := S2 797 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 797 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 797 g797 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 412) h  -- d = 412: 5^2 | 454849+1
    rw [show (2:ℕ) ^ 412 = (2 ^ 200) ^ 2 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g454849 : 454849 ∈ P := S2 454849 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 454849 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 454849 g454849 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 422) h  -- d = 422: 3^7 | (2^422+1) prod (p+1), p in {5, 95110361, 197}
    rw [show (2:ℕ) ^ 422 = (2 ^ 200) ^ 2 * 2 ^ 22 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 22 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5 : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num))
    have g95110361 : 95110361 ∈ P := S2 95110361 prime_95110361 (by norm_num) (hnz (by norm_num)) (R 95110361 (by norm_num))
    have g587101 : 587101 ∈ P := S1 587101 (by norm_num) (by norm_num) (hnz (by norm_num)) 95110361 g95110361 (by norm_num)
    have g787 : 787 ∈ P := S1 787 (by norm_num) (by norm_num) (hnz (by norm_num)) 587101 g587101 (by norm_num)
    have g197 : 197 ∈ P := S1 197 (by norm_num) (by norm_num) (hnz (by norm_num)) 787 g787 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b2 := bud_cons b1 g95110361 (by simp) (by norm_num : 3 ^ 4 ∣ 95110361 + 1)
    have b3 := bud_cons b2 g197 (by simp) (by norm_num : 3 ^ 2 ∣ 197 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 428) h  -- d = 428: 5 | 4209809+1, 2168819+1
    rw [show (2:ℕ) ^ 428 = (2 ^ 200) ^ 2 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4209809 : 4209809 ∈ P := S2 4209809 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4209809 (by norm_num))
    have g13012913 : 13012913 ∈ P := S2 13012913 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13012913 (by norm_num))
    have g2168819 : 2168819 ∈ P := S1 2168819 (by norm_num) (by norm_num) (hnz (by norm_num)) 13012913 g13012913 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4209809 g4209809 2168819 g2168819 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 436) h  -- d = 436: 5^2 | 199+1
    rw [show (2:ℕ) ^ 436 = (2 ^ 200) ^ 2 * 2 ^ 36 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 36 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g598193 : 598193 ∈ P := S2 598193 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 598193 (by norm_num))
    have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 598193 g598193 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 446) h  -- d = 446: 5 | 2^446+1, 1088389+1
    rw [show (2:ℕ) ^ 446 = (2 ^ 200) ^ 2 * 2 ^ 46 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 46 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6530333 : 6530333 ∈ P := S2 6530333 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6530333 (by norm_num))
    have g1088389 : 1088389 ∈ P := S1 1088389 (by norm_num) (by norm_num) (hnz (by norm_num)) 6530333 g6530333 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1088389 g1088389 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 452) h  -- d = 452: 3^6 | (2^452+1) prod (p+1), p in {17, 9041, 11, 137, 23}
    rw [show (2:ℕ) ^ 452 = (2 ^ 200) ^ 2 * 2 ^ 52 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 52 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g9041 : 9041 ∈ P := S2 9041 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 9041 (by norm_num))
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 9041 g9041 (by norm_num)
    have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 9041 g9041 (by norm_num)
    have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g9041 (by simp) (by norm_num : 3 ^ 1 ∣ 9041 + 1)
    have b3 := bud_cons b2 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b4 := bud_cons b3 g137 (by simp) (by norm_num : 3 ^ 1 ∣ 137 + 1)
    have b5 := bud_cons b4 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
    exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 454) h  -- d = 454: 5^2 | 5449+1
    rw [show (2:ℕ) ^ 454 = (2 ^ 200) ^ 2 * 2 ^ 54 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 54 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5449 : 5449 ∈ P := S2 5449 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5449 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5449 g5449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 458) h  -- d = 458: 5^2 | 2749+1
    rw [show (2:ℕ) ^ 458 = (2 ^ 200) ^ 2 * 2 ^ 58 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 58 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2749 : 2749 ∈ P := S2 2749 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2749 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2749 g2749 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 466) h  -- d = 466: 13^2 | 30757+1
    rw [show (2:ℕ) ^ 466 = (2 ^ 200) ^ 2 * 2 ^ 66 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 66 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g30757 : 30757 ∈ P := S2 30757 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 30757 (by norm_num))
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 30757 g30757 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 478) h  -- d = 478: 7^2 | 97+1
    rw [show (2:ℕ) ^ 478 = (2 ^ 200) ^ 2 * 2 ^ 78 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 78 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g77852679293 : 77852679293 ∈ P := S2 77852679293 prime_77852679293 (by norm_num) (hnz (by norm_num)) (R 77852679293 (by norm_num))
    have g193 : 193 ∈ P := S1 193 (by norm_num) (by norm_num) (hnz (by norm_num)) 77852679293 g77852679293 (by norm_num)
    have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 193 g193 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 482) h  -- d = 482: 5 | 2^482+1, 15594629+1
    rw [show (2:ℕ) ^ 482 = (2 ^ 200) ^ 2 * 2 ^ 82 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 82 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g15594629 : 15594629 ∈ P := S2 15594629 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 15594629 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 15594629 g15594629 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 502) h  -- d = 502: 31 | 5021+1, 61+1
    rw [show (2:ℕ) ^ 502 = (2 ^ 200) ^ 2 * 2 ^ 102 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 102 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5021 : 5021 ∈ P := S2 5021 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5021 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 5021 g5021 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 508) h  -- d = 508: 19 | 37+1, 3001+1
    rw [show (2:ℕ) ^ 508 = (2 ^ 200) ^ 2 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3108961 : 3108961 ∈ P := S2 3108961 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3108961 (by norm_num))
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 3108961 g3108961 (by norm_num)
    have g42013 : 42013 ∈ P := S1 42013 (by norm_num) (by norm_num) (hnz (by norm_num)) 3108961 g3108961 (by norm_num)
    have g3001 : 3001 ∈ P := S1 3001 (by norm_num) (by norm_num) (hnz (by norm_num)) 42013 g42013 (by norm_num)
    exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 3001 g3001 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 514) h  -- d = 514: 5 | 2^514+1, 28564009+1
    rw [show (2:ℕ) ^ 514 = (2 ^ 200) ^ 2 * 2 ^ 114 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 114 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g28564009 : 28564009 ∈ P := S2 28564009 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 28564009 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 28564009 g28564009 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 526) h  -- d = 526: 5 | 2^526+1, 119929+1
    rw [show (2:ℕ) ^ 526 = (2 ^ 200) ^ 2 * 2 ^ 126 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 126 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g119929 : 119929 ∈ P := S2 119929 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 119929 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 119929 g119929 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 536) h  -- d = 536: 11 | 4289+1, 43+1
    rw [show (2:ℕ) ^ 536 = (2 ^ 200) ^ 2 * 2 ^ 136 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 136 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4289 : 4289 ∈ P := S2 4289 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4289 (by norm_num))
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 4289 g4289 43 g43 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 538) h  -- d = 538: 5 | 2^538+1, 3229+1
    rw [show (2:ℕ) ^ 538 = (2 ^ 200) ^ 2 * 2 ^ 138 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 138 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3229 : 3229 ∈ P := S2 3229 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3229 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 3229 g3229 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 542) h  -- d = 542: 5^2 | 3049+1
    rw [show (2:ℕ) ^ 542 = (2 ^ 200) ^ 2 * 2 ^ 142 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 142 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g97561 : 97561 ∈ P := S2 97561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 97561 (by norm_num))
    have g48781 : 48781 ∈ P := S1 48781 (by norm_num) (by norm_num) (hnz (by norm_num)) 97561 g97561 (by norm_num)
    have g24391 : 24391 ∈ P := S1 24391 (by norm_num) (by norm_num) (hnz (by norm_num)) 48781 g48781 (by norm_num)
    have g3049 : 3049 ∈ P := S1 3049 (by norm_num) (by norm_num) (hnz (by norm_num)) 24391 g24391 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3049 g3049 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 548) h  -- d = 548: 19^2 | 38226289+1
    rw [show (2:ℕ) ^ 548 = (2 ^ 200) ^ 2 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g38226289 : 38226289 ∈ P := S2 38226289 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 38226289 (by norm_num))
    exact S6 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 38226289 g38226289 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 554) h  -- d = 554: 5 | 2^554+1, 1109+1
    rw [show (2:ℕ) ^ 554 = (2 ^ 200) ^ 2 * 2 ^ 154 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 154 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1109 : 1109 ∈ P := S2 1109 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1109 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1109 g1109 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 562) h  -- d = 562: 7 | 3373+1, 3827221+1
    rw [show (2:ℕ) ^ 562 = (2 ^ 200) ^ 2 * 2 ^ 162 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 162 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3373 : 3373 ∈ P := S2 3373 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3373 (by norm_num))
    have g3827221 : 3827221 ∈ P := S2 3827221 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3827221 (by norm_num))
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 3373 g3373 3827221 g3827221 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 568) h  -- d = 568: 5 | 14254355329+1, 179+1
    rw [show (2:ℕ) ^ 568 = (2 ^ 200) ^ 2 * 2 ^ 168 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 168 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14254355329 : 14254355329 ∈ P := S2 14254355329 prime_14254355329 (by norm_num) (hnz (by norm_num)) (R 14254355329 (by norm_num))
    have g179 : 179 ∈ P := S1 179 (by norm_num) (by norm_num) (hnz (by norm_num)) 14254355329 g14254355329 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 14254355329 g14254355329 179 g179 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 586) h  -- d = 586: 17^2 | 22396921+1
    rw [show (2:ℕ) ^ 586 = (2 ^ 200) ^ 2 * 2 ^ 186 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 186 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g22396921 : 22396921 ∈ P := S2 22396921 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 22396921 (by norm_num))
    exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 22396921 g22396921 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 604) h  -- d = 604: 31 | 2417+1, 61+1
    rw [show (2:ℕ) ^ 604 = (2 ^ 200) ^ 3 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2417 : 2417 ∈ P := S2 2417 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2417 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 2417 g2417 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 614) h  -- d = 614: 5 | 2^614+1, 1229+1
    rw [show (2:ℕ) ^ 614 = (2 ^ 200) ^ 3 * 2 ^ 14 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 14 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1229 : 1229 ∈ P := S2 1229 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1229 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1229 g1229 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 622) h  -- d = 622: 61 | 3^5+1, 6221+1
    rw [show (2:ℕ) ^ 622 = (2 ^ 200) ^ 3 * 2 ^ 22 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 22 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6221 : 6221 ∈ P := S2 6221 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6221 (by norm_num))
    exact S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 6221 g6221 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 626) h  -- d = 626: 5 | 2^626+1, 42569+1
    rw [show (2:ℕ) ^ 626 = (2 ^ 200) ^ 3 * 2 ^ 26 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 26 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g42569 : 42569 ∈ P := S2 42569 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 42569 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 42569 g42569 (by norm_num)

set_option maxHeartbeats 22000000 in
theorem even_1 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d ∈ ({628, 632, 634, 652, 662, 674, 694, 698, 712, 718, 724, 758, 766, 776, 778, 788, 794, 802, 808,
      818, 824, 838, 842, 856, 862, 866, 878, 892, 898, 904, 908, 914, 922, 932, 934, 958, 974,
      982, 998, 1006, 1018, 1042, 1046, 1048, 1076, 1082, 1084, 1108, 1126, 1138} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 628) h  -- d = 628: 5 | 3769+1, 29+1
    rw [show (2:ℕ) ^ 628 = (2 ^ 200) ^ 3 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7537 : 7537 ∈ P := S2 7537 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7537 (by norm_num))
    have g3769 : 3769 ∈ P := S1 3769 (by norm_num) (by norm_num) (hnz (by norm_num)) 7537 g7537 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 3769 g3769 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3769 g3769 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 632) h  -- d = 632: 11 | 43+1, 59113+1
    rw [show (2:ℕ) ^ 632 = (2 ^ 200) ^ 3 * 2 ^ 32 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 32 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g286297736737 : 286297736737 ∈ P := S2 286297736737 prime_286297736737 (by norm_num) (hnz (by norm_num)) (R 286297736737 (by norm_num))
    have g11011451413 : 11011451413 ∈ P := S1 11011451413 prime_11011451413 (by norm_num) (hnz (by norm_num)) 286297736737 g286297736737 (by norm_num)
    have g59113 : 59113 ∈ P := S1 59113 (by norm_num) (by norm_num) (hnz (by norm_num)) 11011451413 g11011451413 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 59113 g59113 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 634) h  -- d = 634: 5 | 2^634+1, 19+1
    rw [show (2:ℕ) ^ 634 = (2 ^ 200) ^ 3 * 2 ^ 34 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 34 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g344759057 : 344759057 ∈ P := S2 344759057 prime_344759057 (by norm_num) (hnz (by norm_num)) (R 344759057 (by norm_num))
    have g912061 : 912061 ∈ P := S1 912061 (by norm_num) (by norm_num) (hnz (by norm_num)) 344759057 g344759057 (by norm_num)
    have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 912061 g912061 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 652) h  -- d = 652: 7^2 | 28322881+1
    rw [show (2:ℕ) ^ 652 = (2 ^ 200) ^ 3 * 2 ^ 52 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 52 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g28322881 : 28322881 ∈ P := S2 28322881 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 28322881 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 28322881 g28322881 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 662) h  -- d = 662: 5 | 2^662+1, 79+1
    rw [show (2:ℕ) ^ 662 = (2 ^ 200) ^ 3 * 2 ^ 62 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 62 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g589181 : 589181 ∈ P := S2 589181 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 589181 (by norm_num))
    have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 589181 g589181 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 79 g79 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 674) h  -- d = 674: 5 | 2^674+1, 2549069+1
    rw [show (2:ℕ) ^ 674 = (2 ^ 200) ^ 3 * 2 ^ 74 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 74 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2549069 : 2549069 ∈ P := S2 2549069 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2549069 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 2549069 g2549069 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 694) h  -- d = 694: 31 | 5575597+1, 61+1
    rw [show (2:ℕ) ^ 694 = (2 ^ 200) ^ 3 * 2 ^ 94 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 94 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5575597 : 5575597 ∈ P := S2 5575597 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5575597 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 5575597 g5575597 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 698) h  -- d = 698: 5 | 2^698+1, 59+1
    rw [show (2:ℕ) ^ 698 = (2 ^ 200) ^ 3 * 2 ^ 98 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 98 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8377 : 8377 ∈ P := S2 8377 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8377 (by norm_num))
    have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 8377 g8377 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 59 g59 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 712) h  -- d = 712: 19 | 37+1, 151+1
    rw [show (2:ℕ) ^ 712 = (2 ^ 200) ^ 3 * 2 ^ 112 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 112 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g290497 : 290497 ∈ P := S2 290497 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 290497 (by norm_num))
    have g11173 : 11173 ∈ P := S1 11173 (by norm_num) (by norm_num) (hnz (by norm_num)) 290497 g290497 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 11173 g11173 (by norm_num)
    have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 11173 g11173 (by norm_num)
    exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 151 g151 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 718) h  -- d = 718: 5 | 2^718+1, 585889+1
    rw [show (2:ℕ) ^ 718 = (2 ^ 200) ^ 3 * 2 ^ 118 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 118 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g585889 : 585889 ∈ P := S2 585889 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 585889 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 585889 g585889 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 724) h  -- d = 724: 3^6 | (2^724+1) prod (p+1), p in {17, 2897, 23, 11}
    rw [show (2:ℕ) ^ 724 = (2 ^ 200) ^ 3 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g2897 : 2897 ∈ P := S2 2897 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2897 (by norm_num))
    have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 2897 g2897 (by norm_num)
    have g304081 : 304081 ∈ P := S2 304081 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 304081 (by norm_num))
    have g152041 : 152041 ∈ P := S1 152041 (by norm_num) (by norm_num) (hnz (by norm_num)) 304081 g304081 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 152041 g152041 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g2897 (by simp) (by norm_num : 3 ^ 2 ∣ 2897 + 1)
    have b3 := bud_cons b2 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
    have b4 := bud_cons b3 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 758) h  -- d = 758: 5^2 | 4549+1
    rw [show (2:ℕ) ^ 758 = (2 ^ 200) ^ 3 * 2 ^ 158 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 158 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4549 : 4549 ∈ P := S2 4549 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4549 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4549 g4549 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 766) h  -- d = 766: 11^2 | 4597+1
    rw [show (2:ℕ) ^ 766 = (2 ^ 200) ^ 3 * 2 ^ 166 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 166 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4597 : 4597 ∈ P := S2 4597 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4597 (by norm_num))
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 4597 g4597 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 776) h  -- d = 776: 11 | 782209+1, 43+1
    rw [show (2:ℕ) ^ 776 = (2 ^ 200) ^ 3 * 2 ^ 176 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 176 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g782209 : 782209 ∈ P := S2 782209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 782209 (by norm_num))
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 782209 g782209 43 g43 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 778) h  -- d = 778: 5^2 | 51349+1
    rw [show (2:ℕ) ^ 778 = (2 ^ 200) ^ 3 * 2 ^ 178 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 178 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g51349 : 51349 ∈ P := S2 51349 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 51349 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 51349 g51349 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 788) h  -- d = 788: 3^6 | (2^788+1) prod (p+1), p in {17, 72497, 281, 11, 47}
    rw [show (2:ℕ) ^ 788 = (2 ^ 200) ^ 3 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g72497 : 72497 ∈ P := S2 72497 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 72497 (by norm_num))
    have g281 : 281 ∈ P := S1 281 (by norm_num) (by norm_num) (hnz (by norm_num)) 72497 g72497 (by norm_num)
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 72497 g72497 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
    have g47 : 47 ∈ P := S1 47 (by norm_num) (by norm_num) (hnz (by norm_num)) 281 g281 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g72497 (by simp) (by norm_num : 3 ^ 1 ∣ 72497 + 1)
    have b3 := bud_cons b2 g281 (by simp) (by norm_num : 3 ^ 1 ∣ 281 + 1)
    have b4 := bud_cons b3 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b5 := bud_cons b4 g47 (by simp) (by norm_num : 3 ^ 1 ∣ 47 + 1)
    exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 794) h  -- d = 794: 5 | 2^794+1, 25409+1
    rw [show (2:ℕ) ^ 794 = (2 ^ 200) ^ 3 * 2 ^ 194 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 194 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g25409 : 25409 ∈ P := S2 25409 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 25409 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 25409 g25409 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 802) h  -- d = 802: 5 | 2^802+1, 3209+1
    rw [show (2:ℕ) ^ 802 = (2 ^ 200) ^ 4 * 2 ^ 2 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 2 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3209 : 3209 ∈ P := S2 3209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3209 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 3209 g3209 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 808) h  -- d = 808: 61 | 3^5+1, 203617+1
    rw [show (2:ℕ) ^ 808 = (2 ^ 200) ^ 4 * 2 ^ 8 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 8 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g203617 : 203617 ∈ P := S2 203617 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 203617 (by norm_num))
    exact S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 203617 g203617 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 818) h  -- d = 818: 5 | 2^818+1, 4909+1
    rw [show (2:ℕ) ^ 818 = (2 ^ 200) ^ 4 * 2 ^ 18 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 18 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4909 : 4909 ∈ P := S2 4909 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4909 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 4909 g4909 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 824) h  -- d = 824: 31 | 19777+1, 61+1
    rw [show (2:ℕ) ^ 824 = (2 ^ 200) ^ 4 * 2 ^ 24 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 24 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g19777 : 19777 ∈ P := S2 19777 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 19777 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 19777 g19777 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 838) h  -- d = 838: 5 | 2^838+1, 63689+1
    rw [show (2:ℕ) ^ 838 = (2 ^ 200) ^ 4 * 2 ^ 38 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 38 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g63689 : 63689 ∈ P := S2 63689 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 63689 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 63689 g63689 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 842) h  -- d = 842: 5 | 2^842+1, 829+1
    rw [show (2:ℕ) ^ 842 = (2 ^ 200) ^ 4 * 2 ^ 42 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 42 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g31142213 : 31142213 ∈ P := S2 31142213 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 31142213 (by norm_num))
    have g829 : 829 ∈ P := S1 829 (by norm_num) (by norm_num) (hnz (by norm_num)) 31142213 g31142213 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 829 g829 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 856) h  -- d = 856: 11 | 43+1, 744721+1
    rw [show (2:ℕ) ^ 856 = (2 ^ 200) ^ 4 * 2 ^ 56 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 56 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g1489441 : 1489441 ∈ P := S2 1489441 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1489441 (by norm_num))
    have g744721 : 744721 ∈ P := S1 744721 (by norm_num) (by norm_num) (hnz (by norm_num)) 1489441 g1489441 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 744721 g744721 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 862) h  -- d = 862: 7^2 | 97+1
    rw [show (2:ℕ) ^ 862 = (2 ^ 200) ^ 4 * 2 ^ 62 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 62 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g91373 : 91373 ∈ P := S2 91373 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 91373 (by norm_num))
    have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 91373 g91373 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 866) h  -- d = 866: 17^2 | 1733+1
    rw [show (2:ℕ) ^ 866 = (2 ^ 200) ^ 4 * 2 ^ 66 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 66 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1733 : 1733 ∈ P := S2 1733 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1733 (by norm_num))
    exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 1733 g1733 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 878) h  -- d = 878: 37 | 695377+1, 9397+1
    rw [show (2:ℕ) ^ 878 = (2 ^ 200) ^ 4 * 2 ^ 78 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 78 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g695377 : 695377 ∈ P := S2 695377 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 695377 (by norm_num))
    have g9397 : 9397 ∈ P := S1 9397 (by norm_num) (by norm_num) (hnz (by norm_num)) 695377 g695377 (by norm_num)
    exact absurd (S3 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 695377 g695377 9397 g9397 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 892) h  -- d = 892: 5 | 19+1, 3329+1
    rw [show (2:ℕ) ^ 892 = (2 ^ 200) ^ 4 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1391521 : 1391521 ∈ P := S2 1391521 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1391521 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 1391521 g1391521 (by norm_num)
    have g3329 : 3329 ∈ P := S1 3329 (by norm_num) (by norm_num) (hnz (by norm_num)) 1391521 g1391521 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 3329 g3329 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 898) h  -- d = 898: 5^2 | 3615349+1
    rw [show (2:ℕ) ^ 898 = (2 ^ 200) ^ 4 * 2 ^ 98 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 98 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3615349 : 3615349 ∈ P := S2 3615349 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3615349 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3615349 g3615349 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 904) h  -- d = 904: 3^6 | (2^904+1) prod (p+1), p in {257, 3617, 5, 23}
    rw [show (2:ℕ) ^ 904 = (2 ^ 200) ^ 4 * 2 ^ 104 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 104 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g3617 : 3617 ∈ P := S2 3617 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3617 (by norm_num))
    have g65089 : 65089 ∈ P := S2 65089 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 65089 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 65089 g65089 (by norm_num)
    have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 65089 g65089 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g3617 (by simp) (by norm_num : 3 ^ 3 ∣ 3617 + 1)
    have b3 := bud_cons b2 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b4 := bud_cons b3 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 908) h  -- d = 908: 17 | 2^908+1, 83537+1
    rw [show (2:ℕ) ^ 908 = (2 ^ 200) ^ 4 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g83537 : 83537 ∈ P := S2 83537 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 83537 (by norm_num))
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 83537 g83537 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 914) h  -- d = 914: 5 | 2^914+1, 829+1
    rw [show (2:ℕ) ^ 914 = (2 ^ 200) ^ 4 * 2 ^ 114 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 114 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g71293 : 71293 ∈ P := S2 71293 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 71293 (by norm_num))
    have g829 : 829 ∈ P := S1 829 (by norm_num) (by norm_num) (hnz (by norm_num)) 71293 g71293 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 829 g829 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 922) h  -- d = 922: 5 | 2^922+1, 7278269+1
    rw [show (2:ℕ) ^ 922 = (2 ^ 200) ^ 4 * 2 ^ 122 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 122 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7278269 : 7278269 ∈ P := S2 7278269 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7278269 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 7278269 g7278269 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 932) h  -- d = 932: 17^2 | 74561+1
    rw [show (2:ℕ) ^ 932 = (2 ^ 200) ^ 4 * 2 ^ 132 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 132 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g74561 : 74561 ∈ P := S2 74561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 74561 (by norm_num))
    exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 74561 g74561 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 934) h  -- d = 934: 7 | 252181+1, 13+1
    rw [show (2:ℕ) ^ 934 = (2 ^ 200) ^ 4 * 2 ^ 134 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 134 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g252181 : 252181 ∈ P := S2 252181 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 252181 (by norm_num))
    have g1372981 : 1372981 ∈ P := S2 1372981 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1372981 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1372981 g1372981 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 252181 g252181 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 958) h  -- d = 958: 11 | 39557737+1, 571+1
    rw [show (2:ℕ) ^ 958 = (2 ^ 200) ^ 4 * 2 ^ 158 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 158 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g39557737 : 39557737 ∈ P := S2 39557737 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 39557737 (by norm_num))
    have g571 : 571 ∈ P := S1 571 (by norm_num) (by norm_num) (hnz (by norm_num)) 39557737 g39557737 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 39557737 g39557737 571 g571 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 974) h  -- d = 974: 5^2 | 1949+1
    rw [show (2:ℕ) ^ 974 = (2 ^ 200) ^ 4 * 2 ^ 174 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 174 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1949 : 1949 ∈ P := S2 1949 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1949 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1949 g1949 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 982) h  -- d = 982: 5 | 2^982+1, 3929+1
    rw [show (2:ℕ) ^ 982 = (2 ^ 200) ^ 4 * 2 ^ 182 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 182 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3929 : 3929 ∈ P := S2 3929 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3929 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 3929 g3929 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 998) h  -- d = 998: 5^2 | 2099+1
    rw [show (2:ℕ) ^ 998 = (2 ^ 200) ^ 4 * 2 ^ 198 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 198 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1179637 : 1179637 ∈ P := S2 1179637 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1179637 (by norm_num))
    have g2099 : 2099 ∈ P := S1 2099 (by norm_num) (by norm_num) (hnz (by norm_num)) 1179637 g1179637 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2099 g2099 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1006) h  -- d = 1006: 5 | 2^1006+1, 3019+1
    rw [show (2:ℕ) ^ 1006 = (2 ^ 200) ^ 5 * 2 ^ 6 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 6 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6037 : 6037 ∈ P := S2 6037 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6037 (by norm_num))
    have g3019 : 3019 ∈ P := S1 3019 (by norm_num) (by norm_num) (hnz (by norm_num)) 6037 g6037 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 3019 g3019 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1018) h  -- d = 1018: 7 | 4073+1, 103837+1
    rw [show (2:ℕ) ^ 1018 = (2 ^ 200) ^ 5 * 2 ^ 18 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 18 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4073 : 4073 ∈ P := S2 4073 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4073 (by norm_num))
    have g103837 : 103837 ∈ P := S2 103837 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 103837 (by norm_num))
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 4073 g4073 103837 g103837 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1042) h  -- d = 1042: 5^2 | 199+1
    rw [show (2:ℕ) ^ 1042 = (2 ^ 200) ^ 5 * 2 ^ 42 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 42 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g16673 : 16673 ∈ P := S2 16673 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16673 (by norm_num))
    have g397 : 397 ∈ P := S1 397 (by norm_num) (by norm_num) (hnz (by norm_num)) 16673 g16673 (by norm_num)
    have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 397 g397 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1046) h  -- d = 1046: 5 | 2^1046+1, 8369+1
    rw [show (2:ℕ) ^ 1046 = (2 ^ 200) ^ 5 * 2 ^ 46 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 46 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8369 : 8369 ∈ P := S2 8369 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8369 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 8369 g8369 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1048) h  -- d = 1048: 3^6 | (2^1048+1) prod (p+1), p in {257, 1211489, 5, 641}
    rw [show (2:ℕ) ^ 1048 = (2 ^ 200) ^ 5 * 2 ^ 48 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 48 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g1211489 : 1211489 ∈ P := S2 1211489 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1211489 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1211489 g1211489 (by norm_num)
    have g641 : 641 ∈ P := S1 641 (by norm_num) (by norm_num) (hnz (by norm_num)) 1211489 g1211489 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g1211489 (by simp) (by norm_num : 3 ^ 3 ∣ 1211489 + 1)
    have b3 := bud_cons b2 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b4 := bud_cons b3 g641 (by simp) (by norm_num : 3 ^ 1 ∣ 641 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1076) h  -- d = 1076: 5 | 61169+1, 2039+1
    rw [show (2:ℕ) ^ 1076 = (2 ^ 200) ^ 5 * 2 ^ 76 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 76 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4037153 : 4037153 ∈ P := S2 4037153 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4037153 (by norm_num))
    have g61169 : 61169 ∈ P := S1 61169 (by norm_num) (by norm_num) (hnz (by norm_num)) 4037153 g4037153 (by norm_num)
    have g2039 : 2039 ∈ P := S1 2039 (by norm_num) (by norm_num) (hnz (by norm_num)) 61169 g61169 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 61169 g61169 2039 g2039 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1082) h  -- d = 1082: 5 | 2^1082+1, 1281089+1
    rw [show (2:ℕ) ^ 1082 = (2 ^ 200) ^ 5 * 2 ^ 82 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 82 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1281089 : 1281089 ∈ P := S2 1281089 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1281089 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1281089 g1281089 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1084) h  -- d = 1084: 11^2 | 241+1
    rw [show (2:ℕ) ^ 1084 = (2 ^ 200) ^ 5 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4337 : 4337 ∈ P := S2 4337 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4337 (by norm_num))
    have g241 : 241 ∈ P := S1 241 (by norm_num) (by norm_num) (hnz (by norm_num)) 4337 g4337 (by norm_num)
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 241 g241 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1108) h  -- d = 1108: 61 | 3^5+1, 13297+1
    rw [show (2:ℕ) ^ 1108 = (2 ^ 200) ^ 5 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13297 : 13297 ∈ P := S2 13297 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13297 (by norm_num))
    exact S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 13297 g13297 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1126) h  -- d = 1126: 5 | 2^1126+1, 89+1
    rw [show (2:ℕ) ^ 1126 = (2 ^ 200) ^ 5 * 2 ^ 126 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 126 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g51797 : 51797 ∈ P := S2 51797 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 51797 (by norm_num))
    have g89 : 89 ∈ P := S1 89 (by norm_num) (by norm_num) (hnz (by norm_num)) 51797 g51797 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 89 g89 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1138) h  -- d = 1138: 5 | 2^1138+1, 257189+1
    rw [show (2:ℕ) ^ 1138 = (2 ^ 200) ^ 5 * 2 ^ 138 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 138 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257189 : 257189 ∈ P := S2 257189 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257189 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 257189 g257189 (by norm_num)

set_option maxHeartbeats 22000000 in
theorem even_2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d ∈ ({1142, 1154, 1172, 1174, 1198, 1202, 1226, 1234, 1238, 1262, 1294, 1304, 1318, 1324, 1346, 1382,
      1384, 1388, 1396, 1418, 1432, 1438, 1454, 1466, 1468, 1478, 1492, 1502, 1522, 1528, 1544,
      1546, 1574, 1604, 1618, 1622, 1636, 1646, 1654, 1678, 1688, 1698, 1706, 1718, 1726, 1754,
      1756, 1762, 1766, 1784} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1142) h  -- d = 1142: 5 | 2^1142+1, 2768209+1
    rw [show (2:ℕ) ^ 1142 = (2 ^ 200) ^ 5 * 2 ^ 142 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 142 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5536417 : 5536417 ∈ P := S2 5536417 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5536417 (by norm_num))
    have g2768209 : 2768209 ∈ P := S1 2768209 (by norm_num) (by norm_num) (hnz (by norm_num)) 5536417 g5536417 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 2768209 g2768209 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1154) h  -- d = 1154: 5 | 2^1154+1, 2309+1
    rw [show (2:ℕ) ^ 1154 = (2 ^ 200) ^ 5 * 2 ^ 154 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 154 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2309 : 2309 ∈ P := S2 2309 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2309 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 2309 g2309 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1172) h  -- d = 1172: 23^2 | 4231+1
    rw [show (2:ℕ) ^ 1172 = (2 ^ 200) ^ 5 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1345457 : 1345457 ∈ P := S2 1345457 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1345457 (by norm_num))
    have g4231 : 4231 ∈ P := S1 4231 (by norm_num) (by norm_num) (hnz (by norm_num)) 1345457 g1345457 (by norm_num)
    exact S6 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 4231 g4231 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1174) h  -- d = 1174: 5 | 2^1174+1, 6829159+1
    rw [show (2:ℕ) ^ 1174 = (2 ^ 200) ^ 5 * 2 ^ 174 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 174 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13658317 : 13658317 ∈ P := S2 13658317 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13658317 (by norm_num))
    have g6829159 : 6829159 ∈ P := S1 6829159 (by norm_num) (by norm_num) (hnz (by norm_num)) 13658317 g13658317 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 6829159 g6829159 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1198) h  -- d = 1198: 5 | 2^1198+1, 306689+1
    rw [show (2:ℕ) ^ 1198 = (2 ^ 200) ^ 5 * 2 ^ 198 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 198 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g306689 : 306689 ∈ P := S2 306689 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 306689 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 306689 g306689 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1202) h  -- d = 1202: 5 | 2^1202+1, 1279+1
    rw [show (2:ℕ) ^ 1202 = (2 ^ 200) ^ 6 * 2 ^ 2 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 2 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g685141 : 685141 ∈ P := S2 685141 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 685141 (by norm_num))
    have g5113 : 5113 ∈ P := S1 5113 (by norm_num) (by norm_num) (hnz (by norm_num)) 685141 g685141 (by norm_num)
    have g2557 : 2557 ∈ P := S1 2557 (by norm_num) (by norm_num) (hnz (by norm_num)) 5113 g5113 (by norm_num)
    have g1279 : 1279 ∈ P := S1 1279 (by norm_num) (by norm_num) (hnz (by norm_num)) 2557 g2557 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1279 g1279 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1226) h  -- d = 1226: 17^2 | 1733+1
    rw [show (2:ℕ) ^ 1226 = (2 ^ 200) ^ 6 * 2 ^ 26 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 26 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17458241 : 17458241 ∈ P := S2 17458241 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17458241 (by norm_num))
    have g1733 : 1733 ∈ P := S1 1733 (by norm_num) (by norm_num) (hnz (by norm_num)) 17458241 g17458241 (by norm_num)
    exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 1733 g1733 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1234) h  -- d = 1234: 5^2 | 4799+1
    rw [show (2:ℕ) ^ 1234 = (2 ^ 200) ^ 6 * 2 ^ 34 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 34 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g86381 : 86381 ∈ P := S2 86381 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 86381 (by norm_num))
    have g4799 : 4799 ∈ P := S1 4799 (by norm_num) (by norm_num) (hnz (by norm_num)) 86381 g86381 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4799 g4799 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1238) h  -- d = 1238: 5 | 2^1238+1, 59+1
    rw [show (2:ℕ) ^ 1238 = (2 ^ 200) ^ 6 * 2 ^ 38 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 38 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2477 : 2477 ∈ P := S2 2477 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2477 (by norm_num))
    have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 2477 g2477 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 59 g59 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1262) h  -- d = 1262: 5 | 2^1262+1, 18229+1
    rw [show (2:ℕ) ^ 1262 = (2 ^ 200) ^ 6 * 2 ^ 62 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 62 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g328121 : 328121 ∈ P := S2 328121 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 328121 (by norm_num))
    have g18229 : 18229 ∈ P := S1 18229 (by norm_num) (by norm_num) (hnz (by norm_num)) 328121 g328121 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 18229 g18229 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1294) h  -- d = 1294: 7 | 854041+1, 13+1
    rw [show (2:ℕ) ^ 1294 = (2 ^ 200) ^ 6 * 2 ^ 94 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 94 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g854041 : 854041 ∈ P := S2 854041 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 854041 (by norm_num))
    have g9679121 : 9679121 ∈ P := S2 9679121 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 9679121 (by norm_num))
    have g179243 : 179243 ∈ P := S1 179243 (by norm_num) (by norm_num) (hnz (by norm_num)) 9679121 g9679121 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 179243 g179243 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 854041 g854041 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1304) h  -- d = 1304: 3^7 | (2^1304+1) prod (p+1), p in {257, 41729, 182561, 5, 107}
    rw [show (2:ℕ) ^ 1304 = (2 ^ 200) ^ 6 * 2 ^ 104 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 104 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g41729 : 41729 ∈ P := S2 41729 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 41729 (by norm_num))
    have g182561 : 182561 ∈ P := S2 182561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 182561 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 41729 g41729 (by norm_num)
    have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (hnz (by norm_num)) 41729 g41729 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g41729 (by simp) (by norm_num : 3 ^ 1 ∣ 41729 + 1)
    have b3 := bud_cons b2 g182561 (by simp) (by norm_num : 3 ^ 1 ∣ 182561 + 1)
    have b4 := bud_cons b3 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b5 := bud_cons b4 g107 (by simp) (by norm_num : 3 ^ 3 ∣ 107 + 1)
    exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1318) h  -- d = 1318: 7^2 | 293+1
    rw [show (2:ℕ) ^ 1318 = (2 ^ 200) ^ 6 * 2 ^ 118 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 118 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5273 : 5273 ∈ P := S2 5273 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5273 (by norm_num))
    have g293 : 293 ∈ P := S1 293 (by norm_num) (by norm_num) (hnz (by norm_num)) 5273 g5273 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 293 g293 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1324) h  -- d = 1324: 31 | 1085681+1, 61+1
    rw [show (2:ℕ) ^ 1324 = (2 ^ 200) ^ 6 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1085681 : 1085681 ∈ P := S2 1085681 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1085681 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 1085681 g1085681 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1346) h  -- d = 1346: 5^2 | 449+1
    rw [show (2:ℕ) ^ 1346 = (2 ^ 200) ^ 6 * 2 ^ 146 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 146 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2693 : 2693 ∈ P := S2 2693 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2693 (by norm_num))
    have g449 : 449 ∈ P := S1 449 (by norm_num) (by norm_num) (hnz (by norm_num)) 2693 g2693 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 449 g449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1382) h  -- d = 1382: 5 | 2^1382+1, 19+1
    rw [show (2:ℕ) ^ 1382 = (2 ^ 200) ^ 6 * 2 ^ 182 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 182 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g11057 : 11057 ∈ P := S2 11057 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11057 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 11057 g11057 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1384) h  -- d = 1384: 7 | 166081+1, 1483+1
    rw [show (2:ℕ) ^ 1384 = (2 ^ 200) ^ 6 * 2 ^ 184 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 184 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g166081 : 166081 ∈ P := S2 166081 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 166081 (by norm_num))
    have g11863 : 11863 ∈ P := S1 11863 (by norm_num) (by norm_num) (hnz (by norm_num)) 166081 g166081 (by norm_num)
    have g1483 : 1483 ∈ P := S1 1483 (by norm_num) (by norm_num) (hnz (by norm_num)) 11863 g11863 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 166081 g166081 1483 g1483 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1388) h  -- d = 1388: 7^2 | 8329+1
    rw [show (2:ℕ) ^ 1388 = (2 ^ 200) ^ 6 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g16657 : 16657 ∈ P := S2 16657 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16657 (by norm_num))
    have g8329 : 8329 ∈ P := S1 8329 (by norm_num) (by norm_num) (hnz (by norm_num)) 16657 g16657 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 8329 g8329 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1396) h  -- d = 1396: 5 | 150769+1, 359+1
    rw [show (2:ℕ) ^ 1396 = (2 ^ 200) ^ 6 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g150769 : 150769 ∈ P := S2 150769 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 150769 (by norm_num))
    have g15077 : 15077 ∈ P := S1 15077 (by norm_num) (by norm_num) (hnz (by norm_num)) 150769 g150769 (by norm_num)
    have g359 : 359 ∈ P := S1 359 (by norm_num) (by norm_num) (hnz (by norm_num)) 15077 g15077 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 150769 g150769 359 g359 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1418) h  -- d = 1418: 11 | 2837+1, 43+1
    rw [show (2:ℕ) ^ 1418 = (2 ^ 200) ^ 7 * 2 ^ 18 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 18 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2837 : 2837 ∈ P := S2 2837 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2837 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 2837 g2837 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 2837 g2837 43 g43 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1432) h  -- d = 1432: 17^2 | 577+1
    rw [show (2:ℕ) ^ 1432 = (2 ^ 200) ^ 7 * 2 ^ 32 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 32 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6925153 : 6925153 ∈ P := S2 6925153 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6925153 (by norm_num))
    have g577 : 577 ∈ P := S1 577 (by norm_num) (by norm_num) (hnz (by norm_num)) 6925153 g6925153 (by norm_num)
    exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 577 g577 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1438) h  -- d = 1438: 5 | 2^1438+1, 8629+1
    rw [show (2:ℕ) ^ 1438 = (2 ^ 200) ^ 7 * 2 ^ 38 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 38 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8629 : 8629 ∈ P := S2 8629 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8629 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 8629 g8629 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1454) h  -- d = 1454: 5 | 2^1454+1, 2909+1
    rw [show (2:ℕ) ^ 1454 = (2 ^ 200) ^ 7 * 2 ^ 54 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 54 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2909 : 2909 ∈ P := S2 2909 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2909 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 2909 g2909 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1466) h  -- d = 1466: 5^2 | 627449+1
    rw [show (2:ℕ) ^ 1466 = (2 ^ 200) ^ 7 * 2 ^ 66 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 66 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g627449 : 627449 ∈ P := S2 627449 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 627449 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 627449 g627449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1468) h  -- d = 1468: 17 | 2^1468+1, 340577+1
    rw [show (2:ℕ) ^ 1468 = (2 ^ 200) ^ 7 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g340577 : 340577 ∈ P := S2 340577 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 340577 (by norm_num))
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 340577 g340577 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1478) h  -- d = 1478: 5 | 2^1478+1, 29+1
    rw [show (2:ℕ) ^ 1478 = (2 ^ 200) ^ 7 * 2 ^ 78 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 78 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2957 : 2957 ∈ P := S2 2957 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2957 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 2957 g2957 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 29 g29 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1492) h  -- d = 1492: 5^2 | 199+1
    rw [show (2:ℕ) ^ 1492 = (2 ^ 200) ^ 7 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g35809 : 35809 ∈ P := S2 35809 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 35809 (by norm_num))
    have g3581 : 3581 ∈ P := S1 3581 (by norm_num) (by norm_num) (hnz (by norm_num)) 35809 g35809 (by norm_num)
    have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 3581 g3581 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1502) h  -- d = 1502: 7^2 | 4507+1
    rw [show (2:ℕ) ^ 1502 = (2 ^ 200) ^ 7 * 2 ^ 102 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 102 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g9013 : 9013 ∈ P := S2 9013 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 9013 (by norm_num))
    have g4507 : 4507 ∈ P := S1 4507 (by norm_num) (by norm_num) (hnz (by norm_num)) 9013 g9013 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 4507 g4507 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1522) h  -- d = 1522: 5 | 2^1522+1, 82189+1
    rw [show (2:ℕ) ^ 1522 = (2 ^ 200) ^ 7 * 2 ^ 122 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 122 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g82189 : 82189 ∈ P := S2 82189 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 82189 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 82189 g82189 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1528) h  -- d = 1528: 3^7 | (2^1528+1) prod (p+1), p in {257, 6113, 1019, 5, 11, 17}
    rw [show (2:ℕ) ^ 1528 = (2 ^ 200) ^ 7 * 2 ^ 128 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 128 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g6113 : 6113 ∈ P := S2 6113 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6113 (by norm_num))
    have g1019 : 1019 ∈ P := S1 1019 (by norm_num) (by norm_num) (hnz (by norm_num)) 6113 g6113 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1019 g1019 (by norm_num)
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 1019 g1019 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g6113 (by simp) (by norm_num : 3 ^ 1 ∣ 6113 + 1)
    have b3 := bud_cons b2 g1019 (by simp) (by norm_num : 3 ^ 1 ∣ 1019 + 1)
    have b4 := bud_cons b3 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b5 := bud_cons b4 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b6 := bud_cons b5 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    exact budget_kernel3 hP h3P E b6.1 ((pow_dvd_pow 3 (by norm_num)).trans b6.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1544) h  -- d = 1544: 7 | 37057+1, 83+1
    rw [show (2:ℕ) ^ 1544 = (2 ^ 200) ^ 7 * 2 ^ 144 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 144 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g37057 : 37057 ∈ P := S2 37057 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 37057 (by norm_num))
    have g2647 : 2647 ∈ P := S1 2647 (by norm_num) (by norm_num) (hnz (by norm_num)) 37057 g37057 (by norm_num)
    have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 2647 g2647 (by norm_num)
    have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 37057 g37057 83 g83 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1546) h  -- d = 1546: 5 | 2^1546+1, 8979169+1
    rw [show (2:ℕ) ^ 1546 = (2 ^ 200) ^ 7 * 2 ^ 146 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 146 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8979169 : 8979169 ∈ P := S2 8979169 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8979169 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 8979169 g8979169 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1574) h  -- d = 1574: 5 | 2^1574+1, 14121929+1
    rw [show (2:ℕ) ^ 1574 = (2 ^ 200) ^ 7 * 2 ^ 174 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 174 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14121929 : 14121929 ∈ P := S2 14121929 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14121929 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 14121929 g14121929 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1604) h  -- d = 1604: 7^2 | 109073+1
    rw [show (2:ℕ) ^ 1604 = (2 ^ 200) ^ 8 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g109073 : 109073 ∈ P := S2 109073 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 109073 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 109073 g109073 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1618) h  -- d = 1618: 5 | 2^1618+1, 25889+1
    rw [show (2:ℕ) ^ 1618 = (2 ^ 200) ^ 8 * 2 ^ 18 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 18 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g25889 : 25889 ∈ P := S2 25889 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 25889 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 25889 g25889 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1622) h  -- d = 1622: 7 | 2687+1, 83+1
    rw [show (2:ℕ) ^ 1622 = (2 ^ 200) ^ 8 * 2 ^ 22 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 22 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5336381 : 5336381 ∈ P := S2 5336381 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5336381 (by norm_num))
    have g2687 : 2687 ∈ P := S1 2687 (by norm_num) (by norm_num) (hnz (by norm_num)) 5336381 g5336381 (by norm_num)
    have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 5336381 g5336381 (by norm_num)
    have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 2687 g2687 83 g83 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1636) h  -- d = 1636: 11 | 516977+1, 373+1
    rw [show (2:ℕ) ^ 1636 = (2 ^ 200) ^ 8 * 2 ^ 36 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 36 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g516977 : 516977 ∈ P := S2 516977 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 516977 (by norm_num))
    have g373 : 373 ∈ P := S1 373 (by norm_num) (by norm_num) (hnz (by norm_num)) 516977 g516977 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 516977 g516977 373 g373 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1646) h  -- d = 1646: 7 | 19753+1, 83+1
    rw [show (2:ℕ) ^ 1646 = (2 ^ 200) ^ 8 * 2 ^ 46 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 46 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g19753 : 19753 ∈ P := S2 19753 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 19753 (by norm_num))
    have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 19753 g19753 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 19753 g19753 83 g83 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1654) h  -- d = 1654: 5 | 2^1654+1, 36389+1
    rw [show (2:ℕ) ^ 1654 = (2 ^ 200) ^ 8 * 2 ^ 54 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 54 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g36389 : 36389 ∈ P := S2 36389 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 36389 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 36389 g36389 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1678) h  -- d = 1678: 5^2 | 5564249+1
    rw [show (2:ℕ) ^ 1678 = (2 ^ 200) ^ 8 * 2 ^ 78 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 78 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5564249 : 5564249 ∈ P := S2 5564249 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5564249 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5564249 g5564249 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1688) h  -- d = 1688: 23 | 94529+1, 137+1
    rw [show (2:ℕ) ^ 1688 = (2 ^ 200) ^ 8 * 2 ^ 88 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 88 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g94529 : 94529 ∈ P := S2 94529 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 94529 (by norm_num))
    have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 94529 g94529 (by norm_num)
    exact absurd (S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 94529 g94529 137 g137 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1698) h  -- d = 1698: 5 | 2^1698+1, 3830689+1
    rw [show (2:ℕ) ^ 1698 = (2 ^ 200) ^ 8 * 2 ^ 98 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 98 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3830689 : 3830689 ∈ P := S2 3830689 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3830689 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 3830689 g3830689 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1706) h  -- d = 1706: 5 | 2^1706+1, 569+1
    rw [show (2:ℕ) ^ 1706 = (2 ^ 200) ^ 8 * 2 ^ 106 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 106 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3413 : 3413 ∈ P := S2 3413 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3413 (by norm_num))
    have g569 : 569 ∈ P := S1 569 (by norm_num) (by norm_num) (hnz (by norm_num)) 3413 g3413 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 569 g569 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1718) h  -- d = 1718: 5 | 2^1718+1, 389+1
    rw [show (2:ℕ) ^ 1718 = (2 ^ 200) ^ 8 * 2 ^ 118 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 118 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g41233 : 41233 ∈ P := S2 41233 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 41233 (by norm_num))
    have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 41233 g41233 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 389 g389 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1726) h  -- d = 1726: 5 | 2^1726+1, 31069+1
    rw [show (2:ℕ) ^ 1726 = (2 ^ 200) ^ 8 * 2 ^ 126 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 126 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g62137 : 62137 ∈ P := S2 62137 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 62137 (by norm_num))
    have g31069 : 31069 ∈ P := S1 31069 (by norm_num) (by norm_num) (hnz (by norm_num)) 62137 g62137 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 31069 g31069 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1754) h  -- d = 1754: 5 | 2^1754+1, 178909+1
    rw [show (2:ℕ) ^ 1754 = (2 ^ 200) ^ 8 * 2 ^ 154 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 154 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g178909 : 178909 ∈ P := S2 178909 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 178909 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 178909 g178909 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1756) h  -- d = 1756: 5^2 | 149+1
    rw [show (2:ℕ) ^ 1756 = (2 ^ 200) ^ 8 * 2 ^ 156 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 156 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g49169 : 49169 ∈ P := S2 49169 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 49169 (by norm_num))
    have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 49169 g49169 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1762) h  -- d = 1762: 41^2 | 292493+1
    rw [show (2:ℕ) ^ 1762 = (2 ^ 200) ^ 8 * 2 ^ 162 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 162 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g292493 : 292493 ∈ P := S2 292493 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 292493 (by norm_num))
    exact S6 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 292493 g292493 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1766) h  -- d = 1766: 31 | 3533+1, 61+1
    rw [show (2:ℕ) ^ 1766 = (2 ^ 200) ^ 8 * 2 ^ 166 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 166 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3533 : 3533 ∈ P := S2 3533 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3533 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 3533 g3533 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1784) h  -- d = 1784: 7^2 | 43609+1
    rw [show (2:ℕ) ^ 1784 = (2 ^ 200) ^ 8 * 2 ^ 184 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 184 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g784961 : 784961 ∈ P := S2 784961 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 784961 (by norm_num))
    have g43609 : 43609 ∈ P := S1 43609 (by norm_num) (by norm_num) (hnz (by norm_num)) 784961 g784961 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 43609 g43609 (by norm_num)

set_option maxHeartbeats 22000000 in
theorem even_3 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d ∈ ({1796, 1816, 1822, 1838, 1844, 1858, 1864, 1868, 1874, 1882, 1894, 1912, 1934, 1942, 1982, 1994,
      2018, 2026, 2038, 2056, 2062, 2066, 2098, 2102, 2104, 2126, 2138, 2168, 2174, 2182, 2186,
      2188, 2194, 2206, 2216, 2218, 2234, 2238, 2246, 2284, 2302, 2306, 2308, 2326, 2342, 2348,
      2362, 2372, 2374, 2396} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1796) h  -- d = 1796: 5 | 14369+1, 2780209+1
    rw [show (2:ℕ) ^ 1796 = (2 ^ 200) ^ 8 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14369 : 14369 ∈ P := S2 14369 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14369 (by norm_num))
    have g2780209 : 2780209 ∈ P := S2 2780209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2780209 (by norm_num))
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 14369 g14369 2780209 g2780209 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1816) h  -- d = 1816: 5^2 | 50849+1
    rw [show (2:ℕ) ^ 1816 = (2 ^ 200) ^ 9 * 2 ^ 16 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 16 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g50849 : 50849 ∈ P := S2 50849 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 50849 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 50849 g50849 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1822) h  -- d = 1822: 5 | 2^1822+1, 19+1
    rw [show (2:ℕ) ^ 1822 = (2 ^ 200) ^ 9 * 2 ^ 22 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 22 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g29153 : 29153 ∈ P := S2 29153 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 29153 (by norm_num))
    have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 29153 g29153 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 113 g113 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1838) h  -- d = 1838: 5 | 2^1838+1, 15174529+1
    rw [show (2:ℕ) ^ 1838 = (2 ^ 200) ^ 9 * 2 ^ 38 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 38 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g15174529 : 15174529 ∈ P := S2 15174529 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 15174529 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 15174529 g15174529 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1844) h  -- d = 1844: 3^6 | (2^1844+1) prod (p+1), p in {17, 5, 2213}
    rw [show (2:ℕ) ^ 1844 = (2 ^ 200) ^ 9 * 2 ^ 44 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 44 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g22129 : 22129 ∈ P := S2 22129 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 22129 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 22129 g22129 (by norm_num)
    have g2213 : 2213 ∈ P := S1 2213 (by norm_num) (by norm_num) (hnz (by norm_num)) 22129 g22129 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b3 := bud_cons b2 g2213 (by simp) (by norm_num : 3 ^ 3 ∣ 2213 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1858) h  -- d = 1858: 5^2 | 11149+1
    rw [show (2:ℕ) ^ 1858 = (2 ^ 200) ^ 9 * 2 ^ 58 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 58 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g11149 : 11149 ∈ P := S2 11149 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11149 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 11149 g11149 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1864) h  -- d = 1864: 11 | 7457+1, 11407681+1
    rw [show (2:ℕ) ^ 1864 = (2 ^ 200) ^ 9 * 2 ^ 64 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 64 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7457 : 7457 ∈ P := S2 7457 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7457 (by norm_num))
    have g11407681 : 11407681 ∈ P := S2 11407681 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11407681 (by norm_num))
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 7457 g7457 11407681 g11407681 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1868) h  -- d = 1868: 5 | 3019+1, 19+1
    rw [show (2:ℕ) ^ 1868 = (2 ^ 200) ^ 9 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g597761 : 597761 ∈ P := S2 597761 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 597761 (by norm_num))
    have g3019 : 3019 ∈ P := S1 3019 (by norm_num) (by norm_num) (hnz (by norm_num)) 597761 g597761 (by norm_num)
    have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 3019 g3019 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 g151 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3019 g3019 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1874) h  -- d = 1874: 13^2 | 802073+1
    rw [show (2:ℕ) ^ 1874 = (2 ^ 200) ^ 9 * 2 ^ 74 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 74 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g802073 : 802073 ∈ P := S2 802073 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 802073 (by norm_num))
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 802073 g802073 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1882) h  -- d = 1882: 3^6 | (2^1882+1) prod (p+1), p in {5, 3383837, 53}
    rw [show (2:ℕ) ^ 1882 = (2 ^ 200) ^ 9 * 2 ^ 82 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 82 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5 : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num))
    have g3383837 : 3383837 ∈ P := S2 3383837 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3383837 (by norm_num))
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 3383837 g3383837 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b2 := bud_cons b1 g3383837 (by simp) (by norm_num : 3 ^ 2 ∣ 3383837 + 1)
    have b3 := bud_cons b2 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1894) h  -- d = 1894: 7 | 1973+1, 13+1
    rw [show (2:ℕ) ^ 1894 = (2 ^ 200) ^ 9 * 2 ^ 94 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 94 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g189401 : 189401 ∈ P := S2 189401 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 189401 (by norm_num))
    have g31567 : 31567 ∈ P := S1 31567 (by norm_num) (by norm_num) (hnz (by norm_num)) 189401 g189401 (by norm_num)
    have g1973 : 1973 ∈ P := S1 1973 (by norm_num) (by norm_num) (hnz (by norm_num)) 31567 g31567 (by norm_num)
    have g6522937 : 6522937 ∈ P := S2 6522937 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6522937 (by norm_num))
    have g141803 : 141803 ∈ P := S1 141803 (by norm_num) (by norm_num) (hnz (by norm_num)) 6522937 g6522937 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 141803 g141803 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1973 g1973 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1912) h  -- d = 1912: 5^2 | 7649+1
    rw [show (2:ℕ) ^ 1912 = (2 ^ 200) ^ 9 * 2 ^ 112 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 112 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7649 : 7649 ∈ P := S2 7649 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7649 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 7649 g7649 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1934) h  -- d = 1934: 5 | 2^1934+1, 6028279+1
    rw [show (2:ℕ) ^ 1934 = (2 ^ 200) ^ 9 * 2 ^ 134 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 134 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g12056557 : 12056557 ∈ P := S2 12056557 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 12056557 (by norm_num))
    have g6028279 : 6028279 ∈ P := S1 6028279 (by norm_num) (by norm_num) (hnz (by norm_num)) 12056557 g12056557 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 6028279 g6028279 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1942) h  -- d = 1942: 7 | 13+1, 83+1
    rw [show (2:ℕ) ^ 1942 = (2 ^ 200) ^ 9 * 2 ^ 142 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 142 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g19421 : 19421 ∈ P := S2 19421 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 19421 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 19421 g19421 (by norm_num)
    have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 19421 g19421 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 83 g83 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1982) h  -- d = 1982: 5^2 | 27749+1
    rw [show (2:ℕ) ^ 1982 = (2 ^ 200) ^ 9 * 2 ^ 182 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 182 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g27749 : 27749 ∈ P := S2 27749 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 27749 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 27749 g27749 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1994) h  -- d = 1994: 5 | 2^1994+1, 3989+1
    rw [show (2:ℕ) ^ 1994 = (2 ^ 200) ^ 9 * 2 ^ 194 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 194 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3989 : 3989 ∈ P := S2 3989 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3989 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 3989 g3989 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2018) h  -- d = 2018: 5 | 2^2018+1, 12109+1
    rw [show (2:ℕ) ^ 2018 = (2 ^ 200) ^ 10 * 2 ^ 18 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 18 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g12109 : 12109 ∈ P := S2 12109 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 12109 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 12109 g12109 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2026) h  -- d = 2026: 7^2 | 33449261+1
    rw [show (2:ℕ) ^ 2026 = (2 ^ 200) ^ 10 * 2 ^ 26 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 26 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g33449261 : 33449261 ∈ P := S2 33449261 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 33449261 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 33449261 g33449261 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2038) h  -- d = 2038: 11^2 | 207877+1
    rw [show (2:ℕ) ^ 2038 = (2 ^ 200) ^ 10 * 2 ^ 38 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 38 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g207877 : 207877 ∈ P := S2 207877 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 207877 (by norm_num))
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 207877 g207877 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2056) h  -- d = 2056: 257^2 | 2^2056+1
    rw [show (2:ℕ) ^ 2056 = (2 ^ 200) ^ 10 * 2 ^ 56 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 56 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    exact S5 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R (257 * 257) (by norm_num))
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2062) h  -- d = 2062: 3^6 | (2^2062+1) prod (p+1), p in {5, 32993, 181457}
    rw [show (2:ℕ) ^ 2062 = (2 ^ 200) ^ 10 * 2 ^ 62 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 62 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5 : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num))
    have g32993 : 32993 ∈ P := S2 32993 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 32993 (by norm_num))
    have g181457 : 181457 ∈ P := S2 181457 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 181457 (by norm_num))
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b2 := bud_cons b1 g32993 (by simp) (by norm_num : 3 ^ 3 ∣ 32993 + 1)
    have b3 := bud_cons b2 g181457 (by simp) (by norm_num : 3 ^ 2 ∣ 181457 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2066) h  -- d = 2066: 5 | 2^2066+1, 78509+1
    rw [show (2:ℕ) ^ 2066 = (2 ^ 200) ^ 10 * 2 ^ 66 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 66 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g78509 : 78509 ∈ P := S2 78509 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 78509 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 78509 g78509 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2098) h  -- d = 2098: 31 | 61+1, 743+1
    rw [show (2:ℕ) ^ 2098 = (2 ^ 200) ^ 10 * 2 ^ 98 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 98 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    have g4640777 : 4640777 ∈ P := S2 4640777 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4640777 (by norm_num))
    have g743 : 743 ∈ P := S1 743 (by norm_num) (by norm_num) (hnz (by norm_num)) 4640777 g4640777 (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 61 g61 743 g743 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2102) h  -- d = 2102: 5 | 2^2102+1, 92489+1
    rw [show (2:ℕ) ^ 2102 = (2 ^ 200) ^ 10 * 2 ^ 102 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 102 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g92489 : 92489 ∈ P := S2 92489 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 92489 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 92489 g92489 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2104) h  -- d = 2104: 7 | 1091+1, 13+1
    rw [show (2:ℕ) ^ 2104 = (2 ^ 200) ^ 10 * 2 ^ 104 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 104 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g58913 : 58913 ∈ P := S2 58913 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 58913 (by norm_num))
    have g1091 : 1091 ∈ P := S1 1091 (by norm_num) (by norm_num) (hnz (by norm_num)) 58913 g58913 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1091 g1091 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1091 g1091 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2126) h  -- d = 2126: 5 | 2^2126+1, 709+1
    rw [show (2:ℕ) ^ 2126 = (2 ^ 200) ^ 10 * 2 ^ 126 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 126 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4253 : 4253 ∈ P := S2 4253 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4253 (by norm_num))
    have g709 : 709 ∈ P := S1 709 (by norm_num) (by norm_num) (hnz (by norm_num)) 4253 g4253 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 709 g709 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2138) h  -- d = 2138: 5 | 2^2138+1, 12829+1
    rw [show (2:ℕ) ^ 2138 = (2 ^ 200) ^ 10 * 2 ^ 138 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 138 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g25657 : 25657 ∈ P := S2 25657 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 25657 (by norm_num))
    have g12829 : 12829 ∈ P := S1 12829 (by norm_num) (by norm_num) (hnz (by norm_num)) 25657 g25657 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 12829 g12829 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2168) h  -- d = 2168: 7 | 13+1, 41+1
    rw [show (2:ℕ) ^ 2168 = (2 ^ 200) ^ 10 * 2 ^ 168 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 168 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g24403009 : 24403009 ∈ P := S2 24403009 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 24403009 (by norm_num))
    have g2440301 : 2440301 ∈ P := S1 2440301 (by norm_num) (by norm_num) (hnz (by norm_num)) 24403009 g24403009 (by norm_num)
    have g406717 : 406717 ∈ P := S1 406717 (by norm_num) (by norm_num) (hnz (by norm_num)) 2440301 g2440301 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 406717 g406717 (by norm_num)
    have g15643 : 15643 ∈ P := S1 15643 (by norm_num) (by norm_num) (hnz (by norm_num)) 406717 g406717 (by norm_num)
    have g3911 : 3911 ∈ P := S1 3911 (by norm_num) (by norm_num) (hnz (by norm_num)) 15643 g15643 (by norm_num)
    have g163 : 163 ∈ P := S1 163 (by norm_num) (by norm_num) (hnz (by norm_num)) 3911 g3911 (by norm_num)
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 163 g163 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2174) h  -- d = 2174: 5^2 | 4349+1
    rw [show (2:ℕ) ^ 2174 = (2 ^ 200) ^ 10 * 2 ^ 174 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 174 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4349 : 4349 ∈ P := S2 4349 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4349 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4349 g4349 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2182) h  -- d = 2182: 7 | 1637+1, 13+1
    rw [show (2:ℕ) ^ 2182 = (2 ^ 200) ^ 10 * 2 ^ 182 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 182 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13093 : 13093 ∈ P := S2 13093 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13093 (by norm_num))
    have g6547 : 6547 ∈ P := S1 6547 (by norm_num) (by norm_num) (hnz (by norm_num)) 13093 g13093 (by norm_num)
    have g1637 : 1637 ∈ P := S1 1637 (by norm_num) (by norm_num) (hnz (by norm_num)) 6547 g6547 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1637 g1637 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1637 g1637 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2186) h  -- d = 2186: 5^2 | 13155349+1
    rw [show (2:ℕ) ^ 2186 = (2 ^ 200) ^ 10 * 2 ^ 186 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 186 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13155349 : 13155349 ∈ P := S2 13155349 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13155349 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 13155349 g13155349 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2188) h  -- d = 2188: 5 | 1459+1, 19+1
    rw [show (2:ℕ) ^ 2188 = (2 ^ 200) ^ 10 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8753 : 8753 ∈ P := S2 8753 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8753 (by norm_num))
    have g1459 : 1459 ∈ P := S1 1459 (by norm_num) (by norm_num) (hnz (by norm_num)) 8753 g8753 (by norm_num)
    have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 1459 g1459 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1459 g1459 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2194) h  -- d = 2194: 5 | 2^2194+1, 114089+1
    rw [show (2:ℕ) ^ 2194 = (2 ^ 200) ^ 10 * 2 ^ 194 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 194 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g114089 : 114089 ∈ P := S2 114089 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 114089 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 114089 g114089 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2206) h  -- d = 2206: 17^2 | 132361+1
    rw [show (2:ℕ) ^ 2206 = (2 ^ 200) ^ 11 * 2 ^ 6 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 6 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g132361 : 132361 ∈ P := S2 132361 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 132361 (by norm_num))
    exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 132361 g132361 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2216) h  -- d = 2216: 43 | 257+1, 124097+1
    rw [show (2:ℕ) ^ 2216 = (2 ^ 200) ^ 11 * 2 ^ 16 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 16 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g124097 : 124097 ∈ P := S2 124097 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 124097 (by norm_num))
    exact absurd (S3 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 124097 g124097 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2218) h  -- d = 2218: 5 | 2^2218+1, 13309+1
    rw [show (2:ℕ) ^ 2218 = (2 ^ 200) ^ 11 * 2 ^ 18 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 18 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13309 : 13309 ∈ P := S2 13309 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13309 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 13309 g13309 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2234) h  -- d = 2234: 31 | 67021+1, 61+1
    rw [show (2:ℕ) ^ 2234 = (2 ^ 200) ^ 11 * 2 ^ 34 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 34 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g67021 : 67021 ∈ P := S2 67021 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 67021 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 67021 g67021 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2238) h  -- d = 2238: 19^2 | 22381+1
    rw [show (2:ℕ) ^ 2238 = (2 ^ 200) ^ 11 * 2 ^ 38 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 38 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g22381 : 22381 ∈ P := S2 22381 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 22381 (by norm_num))
    exact S6 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 22381 g22381 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2246) h  -- d = 2246: 5 | 2^2246+1, 40429+1
    rw [show (2:ℕ) ^ 2246 = (2 ^ 200) ^ 11 * 2 ^ 46 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 46 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g40429 : 40429 ∈ P := S2 40429 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 40429 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 40429 g40429 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2284) h  -- d = 2284: 5 | 30678689+1, 139+1
    rw [show (2:ℕ) ^ 2284 = (2 ^ 200) ^ 11 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g30678689 : 30678689 ∈ P := S2 30678689 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 30678689 (by norm_num))
    have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 30678689 g30678689 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 30678689 g30678689 139 g139 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2302) h  -- d = 2302: 5 | 2^2302+1, 439+1
    rw [show (2:ℕ) ^ 2302 = (2 ^ 200) ^ 11 * 2 ^ 102 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 102 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g36833 : 36833 ∈ P := S2 36833 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 36833 (by norm_num))
    have g877 : 877 ∈ P := S1 877 (by norm_num) (by norm_num) (hnz (by norm_num)) 36833 g36833 (by norm_num)
    have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 877 g877 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 439 g439 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2306) h  -- d = 2306: 5^2 | 76099+1
    rw [show (2:ℕ) ^ 2306 = (2 ^ 200) ^ 11 * 2 ^ 106 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 106 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g152197 : 152197 ∈ P := S2 152197 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 152197 (by norm_num))
    have g76099 : 76099 ∈ P := S1 76099 (by norm_num) (by norm_num) (hnz (by norm_num)) 152197 g152197 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 76099 g76099 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2308) h  -- d = 2308: 3^6 | (2^2308+1) prod (p+1), p in {17, 11, 1259, 5}
    rw [show (2:ℕ) ^ 2308 = (2 ^ 200) ^ 11 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g27697 : 27697 ∈ P := S2 27697 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 27697 (by norm_num))
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 27697 g27697 (by norm_num)
    have g1259 : 1259 ∈ P := S1 1259 (by norm_num) (by norm_num) (hnz (by norm_num)) 27697 g27697 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1259 g1259 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b3 := bud_cons b2 g1259 (by simp) (by norm_num : 3 ^ 2 ∣ 1259 + 1)
    have b4 := bud_cons b3 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2326) h  -- d = 2326: 5^2 | 152249+1
    rw [show (2:ℕ) ^ 2326 = (2 ^ 200) ^ 11 * 2 ^ 126 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 126 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g37453253 : 37453253 ∈ P := S2 37453253 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 37453253 (by norm_num))
    have g152249 : 152249 ∈ P := S1 152249 (by norm_num) (by norm_num) (hnz (by norm_num)) 37453253 g37453253 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 152249 g152249 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2342) h  -- d = 2342: 19^2 | 13152673+1
    rw [show (2:ℕ) ^ 2342 = (2 ^ 200) ^ 11 * 2 ^ 142 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 142 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13152673 : 13152673 ∈ P := S2 13152673 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13152673 (by norm_num))
    exact S6 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 13152673 g13152673 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2348) h  -- d = 2348: 5 | 1493329+1, 24889+1
    rw [show (2:ℕ) ^ 2348 = (2 ^ 200) ^ 11 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2986657 : 2986657 ∈ P := S2 2986657 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2986657 (by norm_num))
    have g1493329 : 1493329 ∈ P := S1 1493329 (by norm_num) (by norm_num) (hnz (by norm_num)) 2986657 g2986657 (by norm_num)
    have g149333 : 149333 ∈ P := S1 149333 (by norm_num) (by norm_num) (hnz (by norm_num)) 1493329 g1493329 (by norm_num)
    have g24889 : 24889 ∈ P := S1 24889 (by norm_num) (by norm_num) (hnz (by norm_num)) 149333 g149333 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1493329 g1493329 24889 g24889 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2362) h  -- d = 2362: 11^2 | 1369961+1
    rw [show (2:ℕ) ^ 2362 = (2 ^ 200) ^ 11 * 2 ^ 162 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 162 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1369961 : 1369961 ∈ P := S2 1369961 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1369961 (by norm_num))
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 1369961 g1369961 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2372) h  -- d = 2372: 7 | 370033+1, 26431+1
    rw [show (2:ℕ) ^ 2372 = (2 ^ 200) ^ 11 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g370033 : 370033 ∈ P := S2 370033 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 370033 (by norm_num))
    have g26431 : 26431 ∈ P := S1 26431 (by norm_num) (by norm_num) (hnz (by norm_num)) 370033 g370033 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 370033 g370033 26431 g26431 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2374) h  -- d = 2374: 23 | 151937+1, 367+1
    rw [show (2:ℕ) ^ 2374 = (2 ^ 200) ^ 11 * 2 ^ 174 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 174 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g151937 : 151937 ∈ P := S2 151937 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 151937 (by norm_num))
    have g367 : 367 ∈ P := S1 367 (by norm_num) (by norm_num) (hnz (by norm_num)) 151937 g151937 (by norm_num)
    exact absurd (S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 151937 g151937 367 g367 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2396) h  -- d = 2396: 3^6 | (2^2396+1) prod (p+1), p in {17, 647}
    rw [show (2:ℕ) ^ 2396 = (2 ^ 200) ^ 11 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g1178833 : 1178833 ∈ P := S2 1178833 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1178833 (by norm_num))
    have g647 : 647 ∈ P := S1 647 (by norm_num) (by norm_num) (hnz (by norm_num)) 1178833 g1178833 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g647 (by simp) (by norm_num : 3 ^ 4 ∣ 647 + 1)
    exact budget_kernel3 hP h3P E b2.1 ((pow_dvd_pow 3 (by norm_num)).trans b2.2)

set_option maxHeartbeats 21600000 in
theorem even_4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d ∈ ({2402, 2428, 2434, 2446, 2458, 2462, 2468, 2474, 2498, 2518, 2524, 2536, 2554, 2564, 2566, 2572,
      2578, 2582, 2594, 2602, 2606, 2612, 2614, 2636, 2638, 2644, 2648, 2654, 2692, 2722, 2734,
      2762, 2764, 2778, 2798, 2818, 2824, 2846, 2854, 2858, 2878, 2902, 2906, 2908, 2932, 2942,
      2962, 2966, 2972} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2402) h  -- d = 2402: 5 | 2^2402+1, 10938709+1
    rw [show (2:ℕ) ^ 2402 = (2 ^ 200) ^ 12 * 2 ^ 2 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 2 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g10938709 : 10938709 ∈ P := S2 10938709 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 10938709 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 10938709 g10938709 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2428) h  -- d = 2428: 5 | 475889+1, 29+1
    rw [show (2:ℕ) ^ 2428 = (2 ^ 200) ^ 12 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g475889 : 475889 ∈ P := S2 475889 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 475889 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 475889 g475889 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 475889 g475889 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2434) h  -- d = 2434: 5 | 2^2434+1, 321289+1
    rw [show (2:ℕ) ^ 2434 = (2 ^ 200) ^ 12 * 2 ^ 34 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 34 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g321289 : 321289 ∈ P := S2 321289 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 321289 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 321289 g321289 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2446) h  -- d = 2446: 5 | 2^2446+1, 44029+1
    rw [show (2:ℕ) ^ 2446 = (2 ^ 200) ^ 12 * 2 ^ 46 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 46 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g44029 : 44029 ∈ P := S2 44029 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 44029 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 44029 g44029 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2458) h  -- d = 2458: 5^2 | 149+1
    rw [show (2:ℕ) ^ 2458 = (2 ^ 200) ^ 12 * 2 ^ 58 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 58 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g9833 : 9833 ∈ P := S2 9833 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 9833 (by norm_num))
    have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 9833 g9833 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2462) h  -- d = 2462: 5 | 2^2462+1, 34469+1
    rw [show (2:ℕ) ^ 2462 = (2 ^ 200) ^ 12 * 2 ^ 62 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 62 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g34469 : 34469 ∈ P := S2 34469 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 34469 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 34469 g34469 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2468) h  -- d = 2468: 5^2 | 124699+1
    rw [show (2:ℕ) ^ 2468 = (2 ^ 200) ^ 12 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4738561 : 4738561 ∈ P := S2 4738561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4738561 (by norm_num))
    have g124699 : 124699 ∈ P := S1 124699 (by norm_num) (by norm_num) (hnz (by norm_num)) 4738561 g4738561 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 124699 g124699 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2474) h  -- d = 2474: 5 | 2^2474+1, 19+1
    rw [show (2:ℕ) ^ 2474 = (2 ^ 200) ^ 12 * 2 ^ 74 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 74 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3265681 : 3265681 ∈ P := S2 3265681 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3265681 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 3265681 g3265681 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2498) h  -- d = 2498: 5 | 2^2498+1, 1019+1
    rw [show (2:ℕ) ^ 2498 = (2 ^ 200) ^ 12 * 2 ^ 98 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 98 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g874301 : 874301 ∈ P := S2 874301 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 874301 (by norm_num))
    have g1019 : 1019 ∈ P := S1 1019 (by norm_num) (by norm_num) (hnz (by norm_num)) 874301 g874301 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1019 g1019 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2518) h  -- d = 2518: 5 | 2^2518+1, 1559+1
    rw [show (2:ℕ) ^ 2518 = (2 ^ 200) ^ 12 * 2 ^ 118 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 118 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g28277141 : 28277141 ∈ P := S2 28277141 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 28277141 (by norm_num))
    have g1559 : 1559 ∈ P := S1 1559 (by norm_num) (by norm_num) (hnz (by norm_num)) 28277141 g28277141 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1559 g1559 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2524) h  -- d = 2524: 17 | 2^2524+1, 4644161+1
    rw [show (2:ℕ) ^ 2524 = (2 ^ 200) ^ 12 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4644161 : 4644161 ∈ P := S2 4644161 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4644161 (by norm_num))
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 4644161 g4644161 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2536) h  -- d = 2536: 5 | 19+1, 89+1
    rw [show (2:ℕ) ^ 2536 = (2 ^ 200) ^ 12 * 2 ^ 136 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 136 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g40577 : 40577 ∈ P := S2 40577 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 40577 (by norm_num))
    have g6763 : 6763 ∈ P := S1 6763 (by norm_num) (by norm_num) (hnz (by norm_num)) 40577 g40577 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 6763 g6763 (by norm_num)
    have g89 : 89 ∈ P := S1 89 (by norm_num) (by norm_num) (hnz (by norm_num)) 6763 g6763 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 89 g89 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2554) h  -- d = 2554: 5^2 | 30649+1
    rw [show (2:ℕ) ^ 2554 = (2 ^ 200) ^ 12 * 2 ^ 154 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 154 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g61297 : 61297 ∈ P := S2 61297 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 61297 (by norm_num))
    have g30649 : 30649 ∈ P := S1 30649 (by norm_num) (by norm_num) (hnz (by norm_num)) 61297 g61297 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 30649 g30649 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2564) h  -- d = 2564: 61 | 3^5+1, 153841+1
    rw [show (2:ℕ) ^ 2564 = (2 ^ 200) ^ 12 * 2 ^ 164 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 164 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g153841 : 153841 ∈ P := S2 153841 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 153841 (by norm_num))
    exact S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 153841 g153841 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2566) h  -- d = 2566: 5 | 2^2566+1, 19+1
    rw [show (2:ℕ) ^ 2566 = (2 ^ 200) ^ 12 * 2 ^ 166 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 166 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g35564761 : 35564761 ∈ P := S2 35564761 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 35564761 (by norm_num))
    have g773147 : 773147 ∈ P := S1 773147 (by norm_num) (by norm_num) (hnz (by norm_num)) 35564761 g35564761 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 773147 g773147 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2572) h  -- d = 2572: 7^2 | 10289+1
    rw [show (2:ℕ) ^ 2572 = (2 ^ 200) ^ 12 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g10289 : 10289 ∈ P := S2 10289 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 10289 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 10289 g10289 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2578) h  -- d = 2578: 5 | 2^2578+1, 2206769+1
    rw [show (2:ℕ) ^ 2578 = (2 ^ 200) ^ 12 * 2 ^ 178 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 178 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2206769 : 2206769 ∈ P := S2 2206769 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2206769 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 2206769 g2206769 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2582) h  -- d = 2582: 61 | 3^5+1, 15493+1
    rw [show (2:ℕ) ^ 2582 = (2 ^ 200) ^ 12 * 2 ^ 182 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 182 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g15493 : 15493 ∈ P := S2 15493 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 15493 (by norm_num))
    exact S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 15493 g15493 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2594) h  -- d = 2594: 5 | 2^2594+1, 5189+1
    rw [show (2:ℕ) ^ 2594 = (2 ^ 200) ^ 12 * 2 ^ 194 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 194 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5189 : 5189 ∈ P := S2 5189 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5189 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 5189 g5189 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2602) h  -- d = 2602: 5 | 2^2602+1, 947129+1
    rw [show (2:ℕ) ^ 2602 = (2 ^ 200) ^ 13 * 2 ^ 2 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 2 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g947129 : 947129 ∈ P := S2 947129 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 947129 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 947129 g947129 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2606) h  -- d = 2606: 17 | 4393717+1, 18461+1
    rw [show (2:ℕ) ^ 2606 = (2 ^ 200) ^ 13 * 2 ^ 6 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 6 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4393717 : 4393717 ∈ P := S2 4393717 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4393717 (by norm_num))
    have g18461 : 18461 ∈ P := S1 18461 (by norm_num) (by norm_num) (hnz (by norm_num)) 4393717 g4393717 (by norm_num)
    exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 4393717 g4393717 18461 g18461 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2612) h  -- d = 2612: 3^7 | (2^2612+1) prod (p+1), p in {17, 20897}
    rw [show (2:ℕ) ^ 2612 = (2 ^ 200) ^ 13 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g20897 : 20897 ∈ P := S2 20897 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 20897 (by norm_num))
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g20897 (by simp) (by norm_num : 3 ^ 5 ∣ 20897 + 1)
    exact budget_kernel3 hP h3P E b2.1 ((pow_dvd_pow 3 (by norm_num)).trans b2.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2614) h  -- d = 2614: 5 | 2^2614+1, 109789+1
    rw [show (2:ℕ) ^ 2614 = (2 ^ 200) ^ 13 * 2 ^ 14 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 14 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g109789 : 109789 ∈ P := S2 109789 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 109789 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 109789 g109789 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2636) h  -- d = 2636: 5 | 21089+1, 19+1
    rw [show (2:ℕ) ^ 2636 = (2 ^ 200) ^ 13 * 2 ^ 36 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 36 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g21089 : 21089 ∈ P := S2 21089 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 21089 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 21089 g21089 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 21089 g21089 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2638) h  -- d = 2638: 5 | 2^2638+1, 1439+1
    rw [show (2:ℕ) ^ 2638 = (2 ^ 200) ^ 13 * 2 ^ 38 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 38 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g31657 : 31657 ∈ P := S2 31657 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 31657 (by norm_num))
    have g1439 : 1439 ∈ P := S1 1439 (by norm_num) (by norm_num) (hnz (by norm_num)) 31657 g31657 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1439 g1439 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2644) h  -- d = 2644: 3^7 | (2^2644+1) prod (p+1), p in {17, 5, 83, 53}
    rw [show (2:ℕ) ^ 2644 = (2 ^ 200) ^ 13 * 2 ^ 44 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 44 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g1396033 : 1396033 ∈ P := S2 1396033 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1396033 (by norm_num))
    have g698017 : 698017 ∈ P := S1 698017 (by norm_num) (by norm_num) (hnz (by norm_num)) 1396033 g1396033 (by norm_num)
    have g829 : 829 ∈ P := S1 829 (by norm_num) (by norm_num) (hnz (by norm_num)) 698017 g698017 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 829 g829 (by norm_num)
    have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 829 g829 (by norm_num)
    have g421 : 421 ∈ P := S1 421 (by norm_num) (by norm_num) (hnz (by norm_num)) 698017 g698017 (by norm_num)
    have g211 : 211 ∈ P := S1 211 (by norm_num) (by norm_num) (hnz (by norm_num)) 421 g421 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 211 g211 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b3 := bud_cons b2 g83 (by simp) (by norm_num : 3 ^ 1 ∣ 83 + 1)
    have b4 := bud_cons b3 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2648) h  -- d = 2648: 7 | 275393+1, 83+1
    rw [show (2:ℕ) ^ 2648 = (2 ^ 200) ^ 13 * 2 ^ 48 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 48 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g275393 : 275393 ∈ P := S2 275393 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 275393 (by norm_num))
    have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 275393 g275393 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 275393 g275393 83 g83 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2654) h  -- d = 2654: 5 | 2^2654+1, 5309+1
    rw [show (2:ℕ) ^ 2654 = (2 ^ 200) ^ 13 * 2 ^ 54 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 54 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5309 : 5309 ∈ P := S2 5309 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5309 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 5309 g5309 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2692) h  -- d = 2692: 3^6 | (2^2692+1) prod (p+1), p in {17, 236897, 41}
    rw [show (2:ℕ) ^ 2692 = (2 ^ 200) ^ 13 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g236897 : 236897 ∈ P := S2 236897 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 236897 (by norm_num))
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 236897 g236897 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g236897 (by simp) (by norm_num : 3 ^ 3 ∣ 236897 + 1)
    have b3 := bud_cons b2 g41 (by simp) (by norm_num : 3 ^ 1 ∣ 41 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2722) h  -- d = 2722: 7^2 | 157877+1
    rw [show (2:ℕ) ^ 2722 = (2 ^ 200) ^ 13 * 2 ^ 122 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 122 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g157877 : 157877 ∈ P := S2 157877 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 157877 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 157877 g157877 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2734) h  -- d = 2734: 5^2 | 199+1
    rw [show (2:ℕ) ^ 2734 = (2 ^ 200) ^ 13 * 2 ^ 134 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 134 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g35427173 : 35427173 ∈ P := S2 35427173 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 35427173 (by norm_num))
    have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 35427173 g35427173 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2762) h  -- d = 2762: 5 | 2^2762+1, 8518009+1
    rw [show (2:ℕ) ^ 2762 = (2 ^ 200) ^ 13 * 2 ^ 162 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 162 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17036017 : 17036017 ∈ P := S2 17036017 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17036017 (by norm_num))
    have g8518009 : 8518009 ∈ P := S1 8518009 (by norm_num) (by norm_num) (hnz (by norm_num)) 17036017 g17036017 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 8518009 g8518009 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2764) h  -- d = 2764: 3^7 | (2^2764+1) prod (p+1), p in {17, 243233, 29, 233}
    rw [show (2:ℕ) ^ 2764 = (2 ^ 200) ^ 13 * 2 ^ 164 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 164 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g243233 : 243233 ∈ P := S2 243233 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 243233 (by norm_num))
    have g13513 : 13513 ∈ P := S1 13513 (by norm_num) (by norm_num) (hnz (by norm_num)) 243233 g243233 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 13513 g13513 (by norm_num)
    have g233 : 233 ∈ P := S1 233 (by norm_num) (by norm_num) (hnz (by norm_num)) 13513 g13513 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g243233 (by simp) (by norm_num : 3 ^ 2 ∣ 243233 + 1)
    have b3 := bud_cons b2 g29 (by simp) (by norm_num : 3 ^ 1 ∣ 29 + 1)
    have b4 := bud_cons b3 g233 (by simp) (by norm_num : 3 ^ 2 ∣ 233 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2778) h  -- d = 2778: 7 | 13+1, 5557+1
    rw [show (2:ℕ) ^ 2778 = (2 ^ 200) ^ 13 * 2 ^ 178 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 178 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13 : 13 ∈ P := S2 13 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13 (by norm_num))
    have g5557 : 5557 ∈ P := S2 5557 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5557 (by norm_num))
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 5557 g5557 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2798) h  -- d = 2798: 5 | 2^2798+1, 1163969+1
    rw [show (2:ℕ) ^ 2798 = (2 ^ 200) ^ 13 * 2 ^ 198 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 198 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1163969 : 1163969 ∈ P := S2 1163969 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1163969 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1163969 g1163969 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2818) h  -- d = 2818: 5 | 2^2818+1, 129629+1
    rw [show (2:ℕ) ^ 2818 = (2 ^ 200) ^ 14 * 2 ^ 18 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 18 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g129629 : 129629 ∈ P := S2 129629 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 129629 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 129629 g129629 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2824) h  -- d = 2824: 5 | 33889+1, 3389+1
    rw [show (2:ℕ) ^ 2824 = (2 ^ 200) ^ 14 * 2 ^ 24 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 24 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g33889 : 33889 ∈ P := S2 33889 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 33889 (by norm_num))
    have g3389 : 3389 ∈ P := S1 3389 (by norm_num) (by norm_num) (hnz (by norm_num)) 33889 g33889 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 33889 g33889 3389 g3389 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2846) h  -- d = 2846: 5 | 2^2846+1, 19+1
    rw [show (2:ℕ) ^ 2846 = (2 ^ 200) ^ 14 * 2 ^ 46 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 46 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5693 : 5693 ∈ P := S2 5693 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5693 (by norm_num))
    have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 5693 g5693 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2854) h  -- d = 2854: 7 | 181+1, 13+1
    rw [show (2:ℕ) ^ 2854 = (2 ^ 200) ^ 14 * 2 ^ 54 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 54 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g713501 : 713501 ∈ P := S2 713501 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 713501 (by norm_num))
    have g181 : 181 ∈ P := S1 181 (by norm_num) (by norm_num) (hnz (by norm_num)) 713501 g713501 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2858) h  -- d = 2858: 3^7 | (2^2858+1) prod (p+1), p in {5, 5717, 953, 53}
    rw [show (2:ℕ) ^ 2858 = (2 ^ 200) ^ 14 * 2 ^ 58 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 58 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5 : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num))
    have g5717 : 5717 ∈ P := S2 5717 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5717 (by norm_num))
    have g953 : 953 ∈ P := S1 953 (by norm_num) (by norm_num) (hnz (by norm_num)) 5717 g5717 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 953 g953 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b2 := bud_cons b1 g5717 (by simp) (by norm_num : 3 ^ 1 ∣ 5717 + 1)
    have b3 := bud_cons b2 g953 (by simp) (by norm_num : 3 ^ 2 ∣ 953 + 1)
    have b4 := bud_cons b3 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2878) h  -- d = 2878: 5 | 2^2878+1, 564089+1
    rw [show (2:ℕ) ^ 2878 = (2 ^ 200) ^ 14 * 2 ^ 78 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 78 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g564089 : 564089 ∈ P := S2 564089 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 564089 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 564089 g564089 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2902) h  -- d = 2902: 5^2 | 6163849+1
    rw [show (2:ℕ) ^ 2902 = (2 ^ 200) ^ 14 * 2 ^ 102 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 102 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6163849 : 6163849 ∈ P := S2 6163849 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6163849 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 6163849 g6163849 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2906) h  -- d = 2906: 5 | 2^2906+1, 19+1
    rw [show (2:ℕ) ^ 2906 = (2 ^ 200) ^ 14 * 2 ^ 106 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 106 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5813 : 5813 ∈ P := S2 5813 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5813 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 5813 g5813 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2908) h  -- d = 2908: 5 | 1093409+1, 21914689+1
    rw [show (2:ℕ) ^ 2908 = (2 ^ 200) ^ 14 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1093409 : 1093409 ∈ P := S2 1093409 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1093409 (by norm_num))
    have g21914689 : 21914689 ∈ P := S2 21914689 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 21914689 (by norm_num))
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1093409 g1093409 21914689 g21914689 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2932) h  -- d = 2932: 3^6 | (2^2932+1) prod (p+1), p in {17, 785777, 53}
    rw [show (2:ℕ) ^ 2932 = (2 ^ 200) ^ 14 * 2 ^ 132 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 132 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g785777 : 785777 ∈ P := S2 785777 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 785777 (by norm_num))
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 785777 g785777 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g785777 (by simp) (by norm_num : 3 ^ 1 ∣ 785777 + 1)
    have b3 := bud_cons b2 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2942) h  -- d = 2942: 5 | 2^2942+1, 109+1
    rw [show (2:ℕ) ^ 2942 = (2 ^ 200) ^ 14 * 2 ^ 142 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 142 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g23537 : 23537 ∈ P := S2 23537 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 23537 (by norm_num))
    have g3923 : 3923 ∈ P := S1 3923 (by norm_num) (by norm_num) (hnz (by norm_num)) 23537 g23537 (by norm_num)
    have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 3923 g3923 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 109 g109 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2962) h  -- d = 2962: 31 | 3424073+1, 61+1
    rw [show (2:ℕ) ^ 2962 = (2 ^ 200) ^ 14 * 2 ^ 162 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 162 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3424073 : 3424073 ∈ P := S2 3424073 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3424073 (by norm_num))
    have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 3424073 g3424073 61 g61 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2966) h  -- d = 2966: 11^2 | 13035571+1
    rw [show (2:ℕ) ^ 2966 = (2 ^ 200) ^ 14 * 2 ^ 166 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 166 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g26071141 : 26071141 ∈ P := S2 26071141 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 26071141 (by norm_num))
    have g13035571 : 13035571 ∈ P := S1 13035571 (by norm_num) (by norm_num) (hnz (by norm_num)) 26071141 g26071141 (by norm_num)
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 13035571 g13035571 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2972) h  -- d = 2972: 5 | 71329+1, 1019+1
    rw [show (2:ℕ) ^ 2972 = (2 ^ 200) ^ 14 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g71329 : 71329 ∈ P := S2 71329 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 71329 (by norm_num))
    have g1019 : 1019 ∈ P := S1 1019 (by norm_num) (by norm_num) (hnz (by norm_num)) 71329 g71329 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 71329 g71329 1019 g1019 (by norm_num) (by norm_num)) (by norm_num)

theorem sieve_even {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d ∈ (({262, 268, 274, 278, 284, 296, 298, 302, 314, 316, 326, 328, 334, 344, 346, 358, 362, 376, 382,
      386, 388, 394, 398, 412, 422, 428, 436, 446, 452, 454, 458, 466, 478, 482, 502, 508, 514,
      526, 536, 538, 542, 548, 554, 562, 568, 586, 604, 614, 622, 626} : Finset ℕ) ∪
      ({628, 632, 634, 652, 662, 674, 694, 698, 712, 718, 724, 758, 766, 776, 778, 788, 794, 802, 808,
      818, 824, 838, 842, 856, 862, 866, 878, 892, 898, 904, 908, 914, 922, 932, 934, 958, 974,
      982, 998, 1006, 1018, 1042, 1046, 1048, 1076, 1082, 1084, 1108, 1126, 1138} : Finset ℕ) ∪
      ({1142, 1154, 1172, 1174, 1198, 1202, 1226, 1234, 1238, 1262, 1294, 1304, 1318, 1324, 1346, 1382,
      1384, 1388, 1396, 1418, 1432, 1438, 1454, 1466, 1468, 1478, 1492, 1502, 1522, 1528, 1544,
      1546, 1574, 1604, 1618, 1622, 1636, 1646, 1654, 1678, 1688, 1698, 1706, 1718, 1726, 1754,
      1756, 1762, 1766, 1784} : Finset ℕ) ∪
      ({1796, 1816, 1822, 1838, 1844, 1858, 1864, 1868, 1874, 1882, 1894, 1912, 1934, 1942, 1982, 1994,
      2018, 2026, 2038, 2056, 2062, 2066, 2098, 2102, 2104, 2126, 2138, 2168, 2174, 2182, 2186,
      2188, 2194, 2206, 2216, 2218, 2234, 2238, 2246, 2284, 2302, 2306, 2308, 2326, 2342, 2348,
      2362, 2372, 2374, 2396} : Finset ℕ) ∪
      ({2402, 2428, 2434, 2446, 2458, 2462, 2468, 2474, 2498, 2518, 2524, 2536, 2554, 2564, 2566, 2572,
      2578, 2582, 2594, 2602, 2606, 2612, 2614, 2636, 2638, 2644, 2648, 2654, 2692, 2722, 2734,
      2762, 2764, 2778, 2798, 2818, 2824, 2846, 2854, 2858, 2878, 2902, 2906, 2908, 2932, 2942,
      2962, 2966, 2972} : Finset ℕ)),
      m % (2 * d) ≠ d := by
  intro d hd
  simp only [Finset.mem_union] at hd
  rcases hd with (((h | h) | h) | h) | h
  · exact even_0 hP h3P E d h
  · exact even_1 hP h3P E d h
  · exact even_2 hP h3P E d h
  · exact even_3 hP h3P E d h
  · exact even_4 hP h3P E d h

-- Section 2. The power of 2 in a.
theorem dbl {a k : ℕ} (h0 : a % k = 0) (h1 : a % (2 * k) ≠ k) : a % (2 * k) = 0 := by
  obtain ⟨t, rfl⟩ := Nat.dvd_of_mod_eq_zero h0
  rcases Nat.even_or_odd' t with ⟨s, rfl | rfl⟩
  · rw [show k * (2 * s) = 2 * k * s by ring]
    exact Nat.mul_mod_right _ _
  · exfalso
    apply h1
    rw [show k * (2 * s + 1) = k + 2 * k * s by ring, Nat.add_mul_mod_self_left]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · exact Nat.mod_eq_of_lt (by omega)

-- With the classes 16, 32, ..., 524288 excluded, 16 | a forces 2^20 | a.
theorem v2_split {a : ℕ}
    (hs : ∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → a % (2 * d) ≠ d)
    (hf : ∀ d ∈ ({512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144,
        524288} : Finset ℕ), a % (2 * d) ≠ d) (h16 : a % 16 = 0) : 1048576 ∣ a := by
  have e1 := dbl (k := 16) h16 (hs 16 (by norm_num) (by norm_num) (by decide))
  have e2 := dbl (k := 32) e1 (hs 32 (by norm_num) (by norm_num) (by decide))
  have e3 := dbl (k := 64) e2 (hs 64 (by norm_num) (by norm_num) (by decide))
  have e4 := dbl (k := 128) e3 (hs 128 (by norm_num) (by norm_num) (by decide))
  have e5 := dbl (k := 256) e4 (hs 256 (by norm_num) (by norm_num) (by decide))
  have e6 := dbl (k := 512) e5 (hf 512 (by simp))
  have e7 := dbl (k := 1024) e6 (hf 1024 (by simp))
  have e8 := dbl (k := 2048) e7 (hf 2048 (by simp))
  have e9 := dbl (k := 4096) e8 (hf 4096 (by simp))
  have e10 := dbl (k := 8192) e9 (hf 8192 (by simp))
  have e11 := dbl (k := 16384) e10 (hf 16384 (by simp))
  have e12 := dbl (k := 32768) e11 (hf 32768 (by simp))
  have e13 := dbl (k := 65536) e12 (hf 65536 (by simp))
  have e14 := dbl (k := 131072) e13 (hf 131072 (by simp))
  have e15 := dbl (k := 262144) e14 (hf 262144 (by simp))
  have e16 := dbl (k := 524288) e15 (hf 524288 (by simp))
  exact Nat.dvd_of_mod_eq_zero e16

-- Section 3. The step.
set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨max A1 (max A2 A3), fun n h hiff he hlo hs hf hc => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hsimple : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he' =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he'⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hsimple
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by simp
  rw [he] at E
  have t1 := sieve_odd hP h3P E
  have t2 := sieve_even hP h3P E
  rw [ha] at t1 t2
  rcases Nat.mod_two_eq_zero_or_one (padicValNat 2 n) with h0 | h1'
  · by_cases h16 : padicValNat 2 n % 16 = 0
    · exact (h3 n h hiff he (v2_split hs hf h16)).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    · exact (h2 n h hiff he hlo h0 h16 hs t2).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h1 n h hiff he hlo h1' hs (hc h1') t1).trans (le_max_left _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1
