import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

-- Reduction CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R3 of step CollatzConjecture.collatz_conjecture.R1.H2.R1.H3
-- Credit: @gmarisi

/-!
# Sharper reduction of the open Collatz no-nontrivial-cycles step

For any periodic point `n ≥ 1000` with `n % 4 = 3` that is the minimum of its cycle:
1. A mod-256 forward stopping-time sieve eliminates 45/64 classes of `n % 4 = 3` in at most
   13 steps, leaving only 19 surviving residue classes mod 256.
2. Exact Crandall–Eliahou cycle inequalities give `3 ^ o < 2 ^ e` and `2 ^ e * n ^ o ≤ (3 * n + 1) ^ o`,
   where `o` and `e` are the odd and even step counts along the cycle (`o + e = k`).
3. Splitting at cutoff `n = 100000` and odd-step count `o = 971` (using `2 ^ 1538 < 3 ^ 971`)
   yields three subgoals:
   * `H1` (finite check): every `1000 ≤ n < 100000` in the 19 surviving mod-256 classes drops below `n`.
   * `H2` (finite Diophantine corridor): for `1 ≤ o < 971`, `3 ^ o < 2 ^ e → 300001 ^ o < 2 ^ e * 100000 ^ o`.
   * `H3` (sharpened open core): `n ≥ 100000`, `n % 256` in the 19 surviving classes,
     `o ≥ 971`, `e ≥ 1539`, `k ≥ 2510`, `o + e = k`, `3 ^ o < 2 ^ e`, and `2 ^ e * n ^ o ≤ (3 * n + 1) ^ o`.
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3

open CollatzConjecture

/-- Finite stopping-time check on `[1000, 100000)` in the 19 surviving mod-256 classes. -/
def H1 : Prop :=
  ∀ n : ℕ, 1000 ≤ n → n < 100000 →
    n % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255] : List ℕ) →
    ∃ i : ℕ, collatzStep^[i] n < n

/-- Finite Diophantine powers corridor at cutoff 100000 for `1 ≤ o < 971`. -/
def H2 : Prop :=
  ∀ o e : ℕ, 1 ≤ o → o < 971 → 3 ^ o < 2 ^ e → 300001 ^ o < 2 ^ e * 100000 ^ o

/-- Sharpened open core: no cycle minimum `n ≥ 100000` in the 19 mod-256 classes with
`o ≥ 971`, `e ≥ 1539`, `k ≥ 2510` satisfying the Crandall–Eliahou corridor. -/
def H3 : Prop :=
  ∀ n k o e : ℕ,
    100000 ≤ n →
    n % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255] : List ℕ) →
    971 ≤ o → 1539 ≤ e → 2510 ≤ k → o + e = k →
    3 ^ o < 2 ^ e →
    2 ^ e * n ^ o ≤ (3 * n + 1) ^ o →
    collatzStep^[k] n = n →
    ∃ i : ℕ, collatzStep^[i] n < n

lemma step_even {m : ℕ} (h : m % 2 = 0) : collatzStep m = m / 2 := by
  unfold collatzStep
  rw [if_pos (Nat.even_iff.mpr h)]

lemma step_odd {m : ℕ} (h : m % 2 = 1) : collatzStep m = 3 * m + 1 := by
  unfold collatzStep
  rw [if_neg (by rw [Nat.even_iff]; omega)]

lemma affine_even {A B q : ℕ} (hA : A % 2 = 0) (hB : B % 2 = 0) :
    collatzStep (A * q + B) = (A / 2) * q + B / 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, A = 2 * a := ⟨A / 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, B = 2 * b := ⟨B / 2, by omega⟩
  have hev : (2 * a * q + 2 * b) % 2 = 0 := by
    rw [show 2 * a * q + 2 * b = 2 * (a * q + b) by ring]
    omega
  rw [step_even hev, show 2 * a * q + 2 * b = 2 * (a * q + b) by ring,
    Nat.mul_div_cancel_left _ (by omega : 0 < 2),
    Nat.mul_div_cancel_left _ (by omega : 0 < 2),
    Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

lemma affine_odd {A B q : ℕ} (hA : A % 2 = 0) (hB : B % 2 = 1) :
    collatzStep (A * q + B) = (3 * A) * q + (3 * B + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, A = 2 * a := ⟨A / 2, by omega⟩
  have hodd : (2 * a * q + B) % 2 = 1 := by
    rw [show 2 * a * q + B = 2 * (a * q) + B by ring]
    omega
  rw [step_odd hodd]
  ring

lemma drop_mod16_3 {n : ℕ} (h : n % 16 = 3) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨6, ?_⟩
  have hq : n = 16 * (n / 16) + 3 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 16) (B := 3) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 48) (B := 10) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 24) (B := 5) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 72) (B := 16) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 36) (B := 8) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 18) (B := 4) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod32_11 {n : ℕ} (h : n % 32 = 11) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨8, ?_⟩
  have hq : n = 32 * (n / 32) + 11 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 32) (B := 11) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 96) (B := 34) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 48) (B := 17) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 144) (B := 52) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 72) (B := 26) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 36) (B := 13) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 108) (B := 40) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 54) (B := 20) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod32_23 {n : ℕ} (h : n % 32 = 23) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨8, ?_⟩
  have hq : n = 32 * (n / 32) + 23 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 32) (B := 23) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 96) (B := 70) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 48) (B := 35) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 144) (B := 106) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 72) (B := 53) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 216) (B := 160) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 108) (B := 80) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 54) (B := 40) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod128_7 {n : ℕ} (h : n % 128 = 7) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨11, ?_⟩
  have hq : n = 128 * (n / 128) + 7 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 128) (B := 7) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 384) (B := 22) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 192) (B := 11) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 576) (B := 34) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 288) (B := 17) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 864) (B := 52) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 432) (B := 26) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 216) (B := 13) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 648) (B := 40) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 324) (B := 20) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 162) (B := 10) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod128_15 {n : ℕ} (h : n % 128 = 15) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨11, ?_⟩
  have hq : n = 128 * (n / 128) + 15 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 128) (B := 15) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 384) (B := 46) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 192) (B := 23) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 576) (B := 70) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 288) (B := 35) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 864) (B := 106) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 432) (B := 53) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1296) (B := 160) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 648) (B := 80) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 324) (B := 40) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 162) (B := 20) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod128_59 {n : ℕ} (h : n % 128 = 59) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨11, ?_⟩
  have hq : n = 128 * (n / 128) + 59 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 128) (B := 59) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 384) (B := 178) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 192) (B := 89) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 576) (B := 268) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 288) (B := 134) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 144) (B := 67) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 432) (B := 202) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 216) (B := 101) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 648) (B := 304) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 324) (B := 152) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 162) (B := 76) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod256_39 {n : ℕ} (h : n % 256 = 39) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨13, ?_⟩
  have hq : n = 256 * (n / 256) + 39 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 256) (B := 39) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 768) (B := 118) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 384) (B := 59) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1152) (B := 178) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 576) (B := 89) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1728) (B := 268) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 864) (B := 134) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 432) (B := 67) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1296) (B := 202) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 648) (B := 101) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1944) (B := 304) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 972) (B := 152) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 486) (B := 76) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod256_79 {n : ℕ} (h : n % 256 = 79) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨13, ?_⟩
  have hq : n = 256 * (n / 256) + 79 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 256) (B := 79) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 768) (B := 238) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 384) (B := 119) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1152) (B := 358) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 576) (B := 179) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1728) (B := 538) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 864) (B := 269) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2592) (B := 808) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1296) (B := 404) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 648) (B := 202) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 324) (B := 101) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 972) (B := 304) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 486) (B := 152) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod256_95 {n : ℕ} (h : n % 256 = 95) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨13, ?_⟩
  have hq : n = 256 * (n / 256) + 95 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 256) (B := 95) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 768) (B := 286) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 384) (B := 143) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1152) (B := 430) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 576) (B := 215) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1728) (B := 646) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 864) (B := 323) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2592) (B := 970) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 1296) (B := 485) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 3888) (B := 1456) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1944) (B := 728) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 972) (B := 364) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 486) (B := 182) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod256_123 {n : ℕ} (h : n % 256 = 123) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨13, ?_⟩
  have hq : n = 256 * (n / 256) + 123 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 256) (B := 123) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 768) (B := 370) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 384) (B := 185) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1152) (B := 556) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 576) (B := 278) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 288) (B := 139) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 864) (B := 418) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 432) (B := 209) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1296) (B := 628) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 648) (B := 314) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 324) (B := 157) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 972) (B := 472) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 486) (B := 236) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod256_175 {n : ℕ} (h : n % 256 = 175) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨13, ?_⟩
  have hq : n = 256 * (n / 256) + 175 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 256) (B := 175) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 768) (B := 526) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 384) (B := 263) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1152) (B := 790) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 576) (B := 395) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1728) (B := 1186) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 864) (B := 593) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 2592) (B := 1780) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1296) (B := 890) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 648) (B := 445) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1944) (B := 1336) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 972) (B := 668) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 486) (B := 334) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod256_199 {n : ℕ} (h : n % 256 = 199) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨13, ?_⟩
  have hq : n = 256 * (n / 256) + 199 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 256) (B := 199) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 768) (B := 598) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 384) (B := 299) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1152) (B := 898) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 576) (B := 449) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1728) (B := 1348) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 864) (B := 674) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 432) (B := 337) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1296) (B := 1012) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 648) (B := 506) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 324) (B := 253) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 972) (B := 760) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 486) (B := 380) (by omega) (by omega)]
  norm_num only
  omega

lemma drop_mod256_219 {n : ℕ} (h : n % 256 = 219) : ∃ i : ℕ, collatzStep^[i] n < n := by
  refine ⟨13, ?_⟩
  have hq : n = 256 * (n / 256) + 219 := by omega
  conv_lhs => rw [hq]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [affine_odd (A := 256) (B := 219) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 768) (B := 658) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 384) (B := 329) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1152) (B := 988) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 576) (B := 494) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 288) (B := 247) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 864) (B := 742) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 432) (B := 371) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1296) (B := 1114) (by omega) (by omega)]
  norm_num only
  rw [affine_odd (A := 648) (B := 557) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 1944) (B := 1672) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 972) (B := 836) (by omega) (by omega)]
  norm_num only
  rw [affine_even (A := 486) (B := 418) (by omega) (by omega)]
  norm_num only
  omega

lemma mod256_sieve {n : ℕ} (h4 : n % 4 = 3) (hmin : ∀ i : ℕ, n ≤ collatzStep^[i] n) :
    n % 256 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255] : List ℕ) := by
  by_cases h_16_3 : n % 16 = 3
  · exact False.elim (by obtain ⟨i, hi⟩ := drop_mod16_3 h_16_3; exact absurd hi (not_lt.mpr (hmin i)))
  by_cases h_32_11 : n % 32 = 11
  · exact False.elim (by obtain ⟨i, hi⟩ := drop_mod32_11 h_32_11; exact absurd hi (not_lt.mpr (hmin i)))
  by_cases h_32_23 : n % 32 = 23
  · exact False.elim (by obtain ⟨i, hi⟩ := drop_mod32_23 h_32_23; exact absurd hi (not_lt.mpr (hmin i)))
  by_cases h_128_7 : n % 128 = 7
  · exact False.elim (by obtain ⟨i, hi⟩ := drop_mod128_7 h_128_7; exact absurd hi (not_lt.mpr (hmin i)))
  by_cases h_128_15 : n % 128 = 15
  · exact False.elim (by obtain ⟨i, hi⟩ := drop_mod128_15 h_128_15; exact absurd hi (not_lt.mpr (hmin i)))
  by_cases h_128_59 : n % 128 = 59
  · exact False.elim (by obtain ⟨i, hi⟩ := drop_mod128_59 h_128_59; exact absurd hi (not_lt.mpr (hmin i)))
  by_cases h_256_39 : n % 256 = 39
  · exact False.elim (by obtain ⟨i, hi⟩ := drop_mod256_39 h_256_39; exact absurd hi (not_lt.mpr (hmin i)))
  by_cases h_256_79 : n % 256 = 79
  · exact False.elim (by obtain ⟨i, hi⟩ := drop_mod256_79 h_256_79; exact absurd hi (not_lt.mpr (hmin i)))
  by_cases h_256_95 : n % 256 = 95
  · exact False.elim (by obtain ⟨i, hi⟩ := drop_mod256_95 h_256_95; exact absurd hi (not_lt.mpr (hmin i)))
  by_cases h_256_123 : n % 256 = 123
  · exact False.elim (by obtain ⟨i, hi⟩ := drop_mod256_123 h_256_123; exact absurd hi (not_lt.mpr (hmin i)))
  by_cases h_256_175 : n % 256 = 175
  · exact False.elim (by obtain ⟨i, hi⟩ := drop_mod256_175 h_256_175; exact absurd hi (not_lt.mpr (hmin i)))
  by_cases h_256_199 : n % 256 = 199
  · exact False.elim (by obtain ⟨i, hi⟩ := drop_mod256_199 h_256_199; exact absurd hi (not_lt.mpr (hmin i)))
  by_cases h_256_219 : n % 256 = 219
  · exact False.elim (by obtain ⟨i, hi⟩ := drop_mod256_219 h_256_219; exact absurd hi (not_lt.mpr (hmin i)))
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

lemma orbit_step_bounds (n : ℕ) (hmin : ∀ i : ℕ, n ≤ collatzStep^[i] n) :
    ∀ t : ℕ, ∃ o e : ℕ, o + e = t ∧
      (o = 0 → 2 ^ e * collatzStep^[t] n = n) ∧
      (0 < o → 3 ^ o * n < 2 ^ e * collatzStep^[t] n) ∧
      2 ^ e * n ^ o * collatzStep^[t] n ≤ (3 * n + 1) ^ o * n := by
  intro t
  induction t with
  | zero =>
    exact ⟨0, 0, rfl, fun _ => by simp, fun h => by omega, by simp⟩
  | succ t ih =>
    obtain ⟨o, e, hsum, hzero, hpos, hup⟩ := ih
    rw [Function.iterate_succ_apply']
    set x := collatzStep^[t] n with hx
    have hnx : n ≤ x := hmin t
    by_cases hev : x % 2 = 0
    · refine ⟨o, e + 1, by omega, ?_, ?_, ?_⟩
      · intro ho
        rw [step_even hev, pow_succ, mul_assoc, show 2 * (x / 2) = x by omega]
        exact hzero ho
      · intro ho
        rw [step_even hev, pow_succ, mul_assoc, show 2 * (x / 2) = x by omega]
        exact hpos ho
      · rw [step_even hev, pow_succ,
          show 2 ^ e * 2 * n ^ o * (x / 2) = 2 ^ e * n ^ o * (2 * (x / 2)) by ring,
          show 2 * (x / 2) = x by omega]
        exact hup
    · have hodd : x % 2 = 1 := by omega
      refine ⟨o + 1, e, by omega, fun h => by omega, ?_, ?_⟩
      · intro _
        rw [step_odd hodd]
        have h2e : 0 < 2 ^ e := Nat.two_pow_pos e
        by_cases ho : o = 0
        · subst ho
          have h0 := hzero rfl
          rw [zero_add, pow_one]
          nlinarith
        · have hp := hpos (by omega)
          rw [pow_succ']
          nlinarith
      · rw [step_odd hodd]
        have hstep : n * (3 * x + 1) ≤ (3 * n + 1) * x := by nlinarith
        calc
          2 ^ e * n ^ (o + 1) * (3 * x + 1)
              = (2 ^ e * n ^ o) * (n * (3 * x + 1)) := by ring
          _ ≤ (2 ^ e * n ^ o) * ((3 * n + 1) * x) := Nat.mul_le_mul_left _ hstep
          _ = (3 * n + 1) * (2 ^ e * n ^ o * x) := by ring
          _ ≤ (3 * n + 1) * ((3 * n + 1) ^ o * n) := Nat.mul_le_mul_left _ hup
          _ = (3 * n + 1) ^ (o + 1) * n := by ring

lemma pow_2_1538_lt_pow_3_971 : 2 ^ 1538 < 3 ^ 971 := by
  have h1 : 2 ^ 84 < 3 ^ 53 := by norm_num
  have h2 : 2 ^ 26 < 3 ^ 17 := by norm_num
  have h3 : (2 ^ 84) ^ 18 < (3 ^ 53) ^ 18 := Nat.pow_lt_pow_left h1 (by omega)
  have h4 : (2 ^ 84) ^ 18 * 2 ^ 26 < (3 ^ 53) ^ 18 * 3 ^ 17 := Nat.mul_lt_mul'' h3 h2
  simpa only [← pow_mul, ← pow_add] using h4

theorem main : H1 → H2 → H3 → OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1.H3 := by
  intro h1 h2 h3 n k hn h4 hk hcyc
  by_contra hno
  push Not at hno
  have hres := mod256_sieve h4 hno
  by_cases hlt : n < 100000
  · obtain ⟨i, hi⟩ := h1 n hn hlt hres
    exact absurd hi (not_lt.mpr (hno i))
  · have hbig : 100000 ≤ n := by omega
    obtain ⟨o, e, hsum, hzero, hpos, hup⟩ := orbit_step_bounds n hno k
    rw [hcyc] at hzero hpos hup
    have ho_pos : 1 ≤ o := by
      by_contra ho0
      have ho' : o = 0 := by omega
      have h0 := hzero ho'
      have he1 : 1 ≤ e := by omega
      have h2e : 2 ≤ 2 ^ e := by
        calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he1
      nlinarith
    have hlow : 3 ^ o < 2 ^ e := by
      have hp := hpos (by omega)
      exact Nat.lt_of_mul_lt_mul_right hp
    have hupper : 2 ^ e * n ^ o ≤ (3 * n + 1) ^ o := by
      exact Nat.le_of_mul_le_mul_right hup (by omega)
    have ho_ge : 971 ≤ o := by
      by_contra ho_lt
      have hcorr := h2 o e ho_pos (by omega) hlow
      have hbase : (3 * n + 1) * 100000 ≤ 300001 * n := by omega
      have hpow : (3 * n + 1) ^ o * 100000 ^ o ≤ 300001 ^ o * n ^ o := by
        rw [← mul_pow, ← mul_pow]
        exact Nat.pow_le_pow_left hbase o
      have hchain : 2 ^ e * 100000 ^ o * n ^ o ≤ 300001 ^ o * n ^ o := by
        calc
          2 ^ e * 100000 ^ o * n ^ o = (2 ^ e * n ^ o) * 100000 ^ o := by ring
          _ ≤ (3 * n + 1) ^ o * 100000 ^ o := Nat.mul_le_mul_right _ hupper
          _ ≤ 300001 ^ o * n ^ o := hpow
      have hnpos : 0 < n ^ o := Nat.pow_pos (by omega)
      have hle : 2 ^ e * 100000 ^ o ≤ 300001 ^ o := Nat.le_of_mul_le_mul_right hchain hnpos
      omega
    have he_ge : 1539 ≤ e := by
      by_contra he_lt
      have he_le : e ≤ 1538 := by omega
      have h1' : 2 ^ e ≤ 2 ^ 1538 := Nat.pow_le_pow_right (by norm_num) he_le
      have h2' : 3 ^ 971 ≤ 3 ^ o := Nat.pow_le_pow_right (by norm_num) ho_ge
      have h3' := pow_2_1538_lt_pow_3_971
      omega
    have hk_ge : 2510 ≤ k := by omega
    obtain ⟨i, hi⟩ := h3 n k o e hbig hres ho_ge he_ge hk_ge hsum hlow hupper hcyc
    exact absurd hi (not_lt.mpr (hno i))

end OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3
