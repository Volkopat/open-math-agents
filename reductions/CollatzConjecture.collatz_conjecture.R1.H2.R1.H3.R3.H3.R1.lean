import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3

-- Reduction CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R3.H3.R1 of step CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R3.H3
-- Credit: @Twalways

/-!
# Mod-1024 sieve and continued-fraction cycle barrier (`k >= 4229, o >= 1636, e >= 2593`) at cutoff 350000

`main` proves two structural strengthenings directly inside Lean:

1. **Mod-1024 forward stopping-time sieve**: all 12 residue classes modulo 1024 inside the 19
   surviving mod-256 classes that contract within 16 steps
   (`287, 347, 367, 423, 507, 575, 583, 735, 815, 923, 975, 999`) are eliminated explicitly via
   affine iteration, leaving only the 64 surviving residue classes modulo 1024.
2. **Continued-fraction semiconvergent barrier at cutoff 350000**: using the lower convergent
   `1054 / 665 < log_2(3)` (`2^1054 < 3^665`), the upper semiconvergent `log_2(3) < 1539 / 971`
   (`3^971 < 2^1539`), the unimodular Farey identity `665 * 1539 - 1054 * 971 = 1`, and the
   elementary induction bound `(x - d) * (x + 1)^d <= x^(d + 1)`, every cycle minimum `n >= 350000`
   must satisfy:
   * **6-digit Diophantine ratio lock**: `1054 * o < 665 * e` and `971 * e < 1539 * o`,
   * **Sharpened period bounds**: `o >= 1636`, `e >= 2593`, and `k >= 4229`.

This splits `R1.H2.R1.H3.R3.H3` cleanly into two steps:

* `H1` (finite stopping-time check, 15625 integers): every `100000 <= n < 350000` in the 64
  surviving mod-1024 classes descends strictly below `n` (max stopping time 267, avg 36.8).
* `H2` (sharpened open cycle core): `n >= 350000`, `n % 1024` in the 64 surviving classes,
  `o >= 1636`, `e >= 2593`, `k >= 4229`, `1054 * o < 665 * e`, `971 * e < 1539 * o`,
  `3 ^ o < 2 ^ e`, `2 ^ e * n ^ o <= (3 * n + 1) ^ o`, and `collatzStep^[k] n = n`.
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3_H3_R1

open CollatzConjecture
open OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3

/-- Finite stopping-time check on `[100000, 350000)` in the 64 surviving residue classes
modulo 1024 (15625 integers total; maximum stopping time is 267). -/
def H1 : Prop :=
  ∀ n : ℕ, 100000 ≤ n → n < 350000 →
    n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
      239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
      767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    ∃ i : ℕ, collatzStep^[i] n < n

/-- Sharpened open cycle core: no cycle minimum `n >= 350000` in the 64 surviving mod-1024
classes with `o >= 1636`, `e >= 2593`, `k >= 4229`, `1054 * o < 665 * e`, and `971 * e < 1539 * o`
satisfies the Crandall-Eliahou corridor. -/
def H2 : Prop :=
  ∀ n k o e : ℕ,
    350000 ≤ n →
    n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
      239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
      767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    1636 ≤ o → 2593 ≤ e → 4229 ≤ k → o + e = k →
    1054 * o < 665 * e →
    971 * e < 1539 * o →
    3 ^ o < 2 ^ e →
    2 ^ e * n ^ o ≤ (3 * n + 1) ^ o →
    collatzStep^[k] n = n →
    ∃ i : ℕ, collatzStep^[i] n < n

lemma drop_mod1024_287 {n : ℕ} (h : n % 1024 = 287) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨16, ?_⟩
  have hq : n = 1024 * (n / 1024) + 287 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 1024) (B := 287) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3072) (B := 862) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1536) (B := 431) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 4608) (B := 1294) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2304) (B := 647) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 6912) (B := 1942) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 3456) (B := 971) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 10368) (B := 2914) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 5184) (B := 1457) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 15552) (B := 4372) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 7776) (B := 2186) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 3888) (B := 1093) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 11664) (B := 3280) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5832) (B := 1640) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2916) (B := 820) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1458) (B := 410) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod1024_347 {n : ℕ} (h : n % 1024 = 347) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨16, ?_⟩
  have hq : n = 1024 * (n / 1024) + 347 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 1024) (B := 347) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3072) (B := 1042) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1536) (B := 521) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 4608) (B := 1564) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2304) (B := 782) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1152) (B := 391) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3456) (B := 1174) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1728) (B := 587) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5184) (B := 1762) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2592) (B := 881) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 7776) (B := 2644) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3888) (B := 1322) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1944) (B := 661) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5832) (B := 1984) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2916) (B := 992) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1458) (B := 496) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod1024_367 {n : ℕ} (h : n % 1024 = 367) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨16, ?_⟩
  have hq : n = 1024 * (n / 1024) + 367 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 1024) (B := 367) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3072) (B := 1102) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1536) (B := 551) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 4608) (B := 1654) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2304) (B := 827) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 6912) (B := 2482) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 3456) (B := 1241) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 10368) (B := 3724) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5184) (B := 1862) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2592) (B := 931) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 7776) (B := 2794) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 3888) (B := 1397) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 11664) (B := 4192) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5832) (B := 2096) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2916) (B := 1048) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1458) (B := 524) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod1024_423 {n : ℕ} (h : n % 1024 = 423) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨16, ?_⟩
  have hq : n = 1024 * (n / 1024) + 423 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 1024) (B := 423) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3072) (B := 1270) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1536) (B := 635) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 4608) (B := 1906) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2304) (B := 953) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 6912) (B := 2860) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3456) (B := 1430) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1728) (B := 715) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5184) (B := 2146) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2592) (B := 1073) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 7776) (B := 3220) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3888) (B := 1610) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1944) (B := 805) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5832) (B := 2416) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2916) (B := 1208) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1458) (B := 604) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod1024_507 {n : ℕ} (h : n % 1024 = 507) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨16, ?_⟩
  have hq : n = 1024 * (n / 1024) + 507 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 1024) (B := 507) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3072) (B := 1522) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1536) (B := 761) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 4608) (B := 2284) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2304) (B := 1142) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1152) (B := 571) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3456) (B := 1714) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1728) (B := 857) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5184) (B := 2572) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2592) (B := 1286) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1296) (B := 643) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3888) (B := 1930) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1944) (B := 965) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5832) (B := 2896) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2916) (B := 1448) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1458) (B := 724) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod1024_575 {n : ℕ} (h : n % 1024 = 575) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨16, ?_⟩
  have hq : n = 1024 * (n / 1024) + 575 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 1024) (B := 575) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3072) (B := 1726) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1536) (B := 863) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 4608) (B := 2590) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2304) (B := 1295) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 6912) (B := 3886) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 3456) (B := 1943) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 10368) (B := 5830) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 5184) (B := 2915) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 15552) (B := 8746) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 7776) (B := 4373) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 23328) (B := 13120) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 11664) (B := 6560) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5832) (B := 3280) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2916) (B := 1640) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1458) (B := 820) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod1024_583 {n : ℕ} (h : n % 1024 = 583) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨16, ?_⟩
  have hq : n = 1024 * (n / 1024) + 583 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 1024) (B := 583) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3072) (B := 1750) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1536) (B := 875) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 4608) (B := 2626) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2304) (B := 1313) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 6912) (B := 3940) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3456) (B := 1970) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1728) (B := 985) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5184) (B := 2956) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2592) (B := 1478) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1296) (B := 739) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3888) (B := 2218) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1944) (B := 1109) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5832) (B := 3328) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2916) (B := 1664) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1458) (B := 832) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod1024_735 {n : ℕ} (h : n % 1024 = 735) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨16, ?_⟩
  have hq : n = 1024 * (n / 1024) + 735 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 1024) (B := 735) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3072) (B := 2206) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1536) (B := 1103) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 4608) (B := 3310) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2304) (B := 1655) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 6912) (B := 4966) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 3456) (B := 2483) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 10368) (B := 7450) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 5184) (B := 3725) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 15552) (B := 11176) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 7776) (B := 5588) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3888) (B := 2794) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1944) (B := 1397) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5832) (B := 4192) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2916) (B := 2096) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1458) (B := 1048) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod1024_815 {n : ℕ} (h : n % 1024 = 815) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨16, ?_⟩
  have hq : n = 1024 * (n / 1024) + 815 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 1024) (B := 815) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3072) (B := 2446) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1536) (B := 1223) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 4608) (B := 3670) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2304) (B := 1835) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 6912) (B := 5506) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 3456) (B := 2753) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 10368) (B := 8260) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5184) (B := 4130) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2592) (B := 2065) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 7776) (B := 6196) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3888) (B := 3098) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1944) (B := 1549) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5832) (B := 4648) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2916) (B := 2324) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1458) (B := 1162) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod1024_923 {n : ℕ} (h : n % 1024 = 923) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨16, ?_⟩
  have hq : n = 1024 * (n / 1024) + 923 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 1024) (B := 923) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3072) (B := 2770) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1536) (B := 1385) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 4608) (B := 4156) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2304) (B := 2078) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1152) (B := 1039) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3456) (B := 3118) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1728) (B := 1559) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5184) (B := 4678) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2592) (B := 2339) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 7776) (B := 7018) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 3888) (B := 3509) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 11664) (B := 10528) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5832) (B := 5264) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2916) (B := 2632) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1458) (B := 1316) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod1024_975 {n : ℕ} (h : n % 1024 = 975) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨16, ?_⟩
  have hq : n = 1024 * (n / 1024) + 975 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 1024) (B := 975) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3072) (B := 2926) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1536) (B := 1463) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 4608) (B := 4390) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2304) (B := 2195) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 6912) (B := 6586) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 3456) (B := 3293) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 10368) (B := 9880) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5184) (B := 4940) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2592) (B := 2470) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1296) (B := 1235) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3888) (B := 3706) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1944) (B := 1853) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5832) (B := 5560) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2916) (B := 2780) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1458) (B := 1390) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod1024_999 {n : ℕ} (h : n % 1024 = 999) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨16, ?_⟩
  have hq : n = 1024 * (n / 1024) + 999 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 1024) (B := 999) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3072) (B := 2998) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1536) (B := 1499) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 4608) (B := 4498) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2304) (B := 2249) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 6912) (B := 6748) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3456) (B := 3374) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1728) (B := 1687) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5184) (B := 5062) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 2592) (B := 2531) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 7776) (B := 7594) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 3888) (B := 3797) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 11664) (B := 11392) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 5832) (B := 5696) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2916) (B := 2848) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1458) (B := 1424) (by omega) (by omega)]
  norm_num only
  omega

lemma elim_mod1024_cases (r : ℕ) (hr : r < 1024)
    (h256 : r % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255] : List ℕ))
    (hnot : r ∉ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
      239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
      767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ)) :
    r = 287 ∨ r = 347 ∨ r = 367 ∨ r = 423 ∨ r = 507 ∨ r = 575 ∨
    r = 583 ∨ r = 735 ∨ r = 815 ∨ r = 923 ∨ r = 975 ∨ r = 999 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h256
  rcases h256 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  · have hq : r / 256 = 0 ∨ r / 256 = 1 ∨ r / 256 = 2 ∨ r / 256 = 3 := by omega
    rcases hq with hq | hq | hq | hq <;>
    · have hr' : r = 256 * (r / 256) + r % 256 := (Nat.div_add_mod r 256).symm
      rw [hq, h] at hr'
      norm_num at hr'
      rw [hr'] at hnot ⊢
      first | (exfalso; exact hnot (by decide)) | decide

lemma bernoulli_pow_bound (x : ℕ) : ∀ d : ℕ, d ≤ x → (x - d) * (x + 1) ^ d ≤ x ^ (d + 1)
  | 0, _ => by simp
  | d + 1, hdx => by
    have hstep : (x - (d + 1)) * (x + 1) ≤ x * (x - d) := by
      have hsub : x - d = x - (d + 1) + 1 := by omega
      have hle : x - (d + 1) ≤ x := Nat.sub_le _ _
      rw [hsub]
      nlinarith
    calc (x - (d + 1)) * (x + 1) ^ (d + 1)
        = (x - (d + 1)) * ((x + 1) * (x + 1) ^ d) := by rw [pow_succ']
      _ = ((x - (d + 1)) * (x + 1)) * (x + 1) ^ d := by rw [mul_assoc]
      _ ≤ (x * (x - d)) * (x + 1) ^ d := Nat.mul_le_mul_right _ hstep
      _ = x * ((x - d) * (x + 1) ^ d) := by rw [mul_assoc]
      _ ≤ x * x ^ (d + 1) := Nat.mul_le_mul_left x (bernoulli_pow_bound x d (by omega))
      _ = x ^ (d + 2) := (pow_succ' x (d + 1)).symm

lemma ratio_mono {e o a b : ℕ} (hab : a ≤ b) (hb : 0 < b)
    (h : 2 ^ e * b ^ o ≤ (3 * b + 1) ^ o) : 2 ^ e * a ^ o ≤ (3 * a + 1) ^ o := by
  have hlin : (3 * b + 1) * a ≤ (3 * a + 1) * b := by nlinarith
  have hpow : (3 * b + 1) ^ o * a ^ o ≤ (3 * a + 1) ^ o * b ^ o := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left hlin o
  have hmul : (2 ^ e * a ^ o) * b ^ o ≤ (3 * a + 1) ^ o * b ^ o := by
    calc (2 ^ e * a ^ o) * b ^ o
        = (2 ^ e * b ^ o) * a ^ o := by ring
      _ ≤ (3 * b + 1) ^ o * a ^ o := Nat.mul_le_mul_right _ h
      _ ≤ (3 * a + 1) ^ o * b ^ o := hpow
  exact Nat.le_of_mul_le_mul_right hmul (pow_pos hb o)

lemma lower_conv : 2 ^ 1054 < 3 ^ 665 := by decide +kernel

lemma upper_conv_cutoff :
    3 * 350000 * 3 ^ 971 < (3 * 350000 - 971) * 2 ^ 1539 := by decide +kernel

lemma upper_cutoff_pow :
    (3 * 350000 + 1) ^ 971 < 2 ^ 1539 * 350000 ^ 971 := by
  have hb := bernoulli_pow_bound (3 * 350000) 971 (by omega)
  have hpow : (3 * 350000) ^ (971 + 1) =
      (3 * 350000 * 3 ^ 971) * 350000 ^ 971 := by
    rw [pow_succ', mul_pow]
    simp only [mul_assoc]
  rw [hpow] at hb
  have hlt : (3 * 350000 - 971) * (3 * 350000 + 1) ^ 971 <
      (3 * 350000 - 971) * (2 ^ 1539 * 350000 ^ 971) := by
    calc (3 * 350000 - 971) * (3 * 350000 + 1) ^ 971
        ≤ (3 * 350000 * 3 ^ 971) * 350000 ^ 971 := hb
      _ < ((3 * 350000 - 971) * 2 ^ 1539) * 350000 ^ 971 :=
          Nat.mul_lt_mul_of_pos_right upper_conv_cutoff (pow_pos (by omega) 971)
      _ = (3 * 350000 - 971) * (2 ^ 1539 * 350000 ^ 971) := by rw [mul_assoc]
  exact Nat.lt_of_mul_lt_mul_left hlt

theorem main : H1 → H2 → OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3.H3 := by
  intro h1 h2 n k o e hn h256 ho971 _ _ hsum h32 hbound hper
  by_cases h1024 : n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207,
      223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795,
      799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ)
  · by_cases hlt : n < 350000
    · exact h1 n hn hlt h1024
    · have hn35 : 350000 ≤ n := by omega
      have ho_pos : 0 < o := by omega
      have h35 : 2 ^ e * 350000 ^ o ≤ (3 * 350000 + 1) ^ o :=
        ratio_mono hn35 (by omega) hbound
      have hlow : 1054 * o < 665 * e := by
        have h1' : (2 ^ 1054) ^ o < (3 ^ 665) ^ o :=
          Nat.pow_lt_pow_left lower_conv (Nat.ne_of_gt ho_pos)
        have h2' : (3 ^ o) ^ 665 < (2 ^ e) ^ 665 :=
          Nat.pow_lt_pow_left h32 (by decide)
        have h3' : 2 ^ (1054 * o) < 2 ^ (665 * e) := by
          calc 2 ^ (1054 * o) = (2 ^ 1054) ^ o := pow_mul 2 1054 o
            _ < (3 ^ 665) ^ o := h1'
            _ = 3 ^ (665 * o) := (pow_mul 3 665 o).symm
            _ = 3 ^ (o * 665) := by rw [mul_comm]
            _ = (3 ^ o) ^ 665 := pow_mul 3 o 665
            _ < (2 ^ e) ^ 665 := h2'
            _ = 2 ^ (e * 665) := (pow_mul 2 e 665).symm
            _ = 2 ^ (665 * e) := by rw [mul_comm]
        exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h3'
      have hhigh : 971 * e < 1539 * o := by
        have h1' : (2 ^ e * 350000 ^ o) ^ 971 ≤ ((3 * 350000 + 1) ^ o) ^ 971 :=
          Nat.pow_le_pow_left h35 971
        have h2' : ((3 * 350000 + 1) ^ 971) ^ o < (2 ^ 1539 * 350000 ^ 971) ^ o :=
          Nat.pow_lt_pow_left upper_cutoff_pow (Nat.ne_of_gt ho_pos)
        have h3' : 2 ^ (971 * e) * 350000 ^ (971 * o) <
            2 ^ (1539 * o) * 350000 ^ (971 * o) := by
          calc 2 ^ (971 * e) * 350000 ^ (971 * o)
              = (2 ^ e * 350000 ^ o) ^ 971 := by
                rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm e 971, mul_comm o 971]
            _ ≤ ((3 * 350000 + 1) ^ o) ^ 971 := h1'
            _ = ((3 * 350000 + 1) ^ 971) ^ o := by
                rw [← pow_mul, ← pow_mul, mul_comm o 971]
            _ < (2 ^ 1539 * 350000 ^ 971) ^ o := h2'
            _ = 2 ^ (1539 * o) * 350000 ^ (971 * o) := by
                rw [mul_pow, ← pow_mul, ← pow_mul]
        have h4' : 2 ^ (971 * e) < 2 ^ (1539 * o) := Nat.lt_of_mul_lt_mul_right h3'
        exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h4'
      have ho_ge : 1636 ≤ o := by omega
      have he_ge : 2593 ≤ e := by omega
      have hk_ge : 4229 ≤ k := by omega
      exact h2 n k o e hn35 h1024 ho_ge he_ge hk_ge hsum hlow hhigh h32 hbound hper
  · have h256' : (n % 1024) % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255] : List ℕ) := by
      have hm : (n % 1024) % 256 = n % 256 := by omega
      rw [hm]
      exact h256
    have hcases := elim_mod1024_cases (n % 1024) (Nat.mod_lt n (by omega)) h256' h1024
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h
    · exact drop_mod1024_287 h
    · exact drop_mod1024_347 h
    · exact drop_mod1024_367 h
    · exact drop_mod1024_423 h
    · exact drop_mod1024_507 h
    · exact drop_mod1024_575 h
    · exact drop_mod1024_583 h
    · exact drop_mod1024_735 h
    · exact drop_mod1024_815 h
    · exact drop_mod1024_923 h
    · exact drop_mod1024_975 h
    · exact drop_mod1024_999 h

end OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3_H3_R1
