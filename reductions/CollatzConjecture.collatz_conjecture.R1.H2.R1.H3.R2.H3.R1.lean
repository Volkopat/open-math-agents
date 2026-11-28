import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2

-- Reduction CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R2.H3.R1 of step CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R2.H3
-- Credit: @Twalways

/-!
# Continued-fraction cycle barrier (`k >= 2510, o >= 971, e >= 1539`) and mod-1024 sieve at cutoff 100000

Applying the adjacent continued-fraction convergents of `log_2(3)`,

* lower convergent `1054 / 665 < log_2(3)` (`2^1054 < 3^665`),
* upper convergent `log_2(3) < 485 / 306` (`3^306 < 2^485`),
* unimodular Farey identity `665 * 485 - 1054 * 306 = 1`,

together with the elementary induction inequality `(x - d) * (x + 1)^d <= x^(d + 1)` at
cutoff `n >= 100000`, `main` proves directly inside Lean that any nontrivial Collatz cycle
minimum `n >= 100000` satisfies:

1. **5-digit Diophantine ratio lock**: `1054 * o < 665 * e` and `306 * e < 485 * o`
   (squeezing `e / o` into an interval of width `4.9 * 10^-6` around `log_2(3)`).
2. **Nearly 5x sharpened period bounds**: `o >= 971` (from `200`), `e >= 1539` (from `317`),
   and `k >= 2510` (from `517`).

This splits `R1.H2.R1.H3.R2.H3` cleanly into three steps:

* `H1` (finite mod-1024 Terras stopping-time sieve): every `n >= 10000` in the 40 eliminated
  classes modulo 1024 (inside the 13 surviving mod-128 classes, outside the 64 surviving
  mod-1024 classes) descends strictly below `n`.
* `H2` (finite stopping-time check, 5625 integers): every `10000 <= n < 100000` in the 64
  surviving mod-1024 classes descends strictly below `n` (max stopping time 220, avg 36.6).
* `H3` (sharpened open cycle core): restricted to `n >= 100000`, the 64 surviving mod-1024
  classes, `k >= 2510`, `o >= 971`, `e >= 1539`, and `1054 * o < 665 * e`, `306 * e < 485 * o`.
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2_H3_R1

open CollatzConjecture

/-- Finite mod-1024 Terras stopping-time sieve: the 40 eliminated classes modulo 1024 inside
the 13 surviving mod-128 classes all descend strictly below `n` for every `n >= 10000`. -/
def H1 : Prop :=
  ∀ n : ℕ, 10000 ≤ n →
    (n % 128 = 27 ∨ n % 128 = 31 ∨ n % 128 = 39 ∨ n % 128 = 47 ∨
     n % 128 = 63 ∨ n % 128 = 71 ∨ n % 128 = 79 ∨ n % 128 = 91 ∨
     n % 128 = 95 ∨ n % 128 = 103 ∨ n % 128 = 111 ∨ n % 128 = 123 ∨ n % 128 = 127) →
    n % 1024 ∉ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
      239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
      767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    ∃ i : ℕ, collatzStep^[i] n < n

/-- Finite stopping-time check on `[10000, 100000)` in the 64 surviving residue classes modulo
1024 (5625 integers total; maximum stopping time is 220). -/
def H2 : Prop :=
  ∀ n : ℕ, 10000 ≤ n → n < 100000 →
    n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
      239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
      767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    ∃ i : ℕ, collatzStep^[i] n < n

/-- Sharpened open cycle core: no periodic point `n >= 100000` in the 64 surviving mod-1024
classes with `k >= 2510`, `o >= 971`, `e >= 1539`, `1054 * o < 665 * e`, `306 * e < 485 * o`,
`3 ^ o < 2 ^ e`, and `2 ^ e * n ^ o <= (3 * n + 1) ^ o` is the minimum of its cycle. -/
def H3 : Prop :=
  ∀ n k : ℕ,
    100000 ≤ n →
    n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
      239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
      767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    2510 ≤ k →
    collatzStep^[k] n = n →
    let e := ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 0)).card
    let o := ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card
    971 ≤ o →
    1539 ≤ e →
    1054 * o < 665 * e →
    306 * e < 485 * o →
    3 ^ o < 2 ^ e →
    2 ^ e * n ^ o ≤ (3 * n + 1) ^ o →
    ∃ i : ℕ, collatzStep^[i] n < n

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
    3 * 100000 * 3 ^ 306 < (3 * 100000 - 306) * 2 ^ 485 := by decide +kernel

lemma upper_cutoff_pow :
    (3 * 100000 + 1) ^ 306 < 2 ^ 485 * 100000 ^ 306 := by
  have hb := bernoulli_pow_bound (3 * 100000) 306 (by omega)
  have hpow : (3 * 100000) ^ (306 + 1) =
      (3 * 100000 * 3 ^ 306) * 100000 ^ 306 := by
    rw [pow_succ', mul_pow]
    simp only [mul_assoc]
  rw [hpow] at hb
  have hlt : (3 * 100000 - 306) * (3 * 100000 + 1) ^ 306 <
      (3 * 100000 - 306) * (2 ^ 485 * 100000 ^ 306) := by
    calc (3 * 100000 - 306) * (3 * 100000 + 1) ^ 306
        ≤ (3 * 100000 * 3 ^ 306) * 100000 ^ 306 := hb
      _ < ((3 * 100000 - 306) * 2 ^ 485) * 100000 ^ 306 :=
          Nat.mul_lt_mul_of_pos_right upper_conv_cutoff (pow_pos (by omega) 306)
      _ = (3 * 100000 - 306) * (2 ^ 485 * 100000 ^ 306) := by rw [mul_assoc]
  exact Nat.lt_of_mul_lt_mul_left hlt

lemma filter_even_add_odd (n : ℕ) : ∀ k : ℕ,
    ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 0)).card +
    ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card = k
  | 0 => by simp
  | k + 1 => by
    rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    have hni : k ∉ Finset.range k := by simp
    have ih := filter_even_add_odd n k
    by_cases h : collatzStep^[k] n % 2 = 0
    · have hni0 : k ∉ (Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 0) := by
        simp [hni]
      simp [h, Finset.card_insert_of_notMem hni0]
      omega
    · have h1 : collatzStep^[k] n % 2 = 1 := by omega
      have hni1 : k ∉ (Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1) := by
        simp [hni]
      simp [h1, Finset.card_insert_of_notMem hni1]
      omega

theorem main : H1 → H2 → H3 → OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2.H3 := by
  intro h1 h2 h3 n k hn h128 _ hper e o ho200 _ h32 hbound
  by_cases h1024 : n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207,
      223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795,
      799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ)
  · by_cases hlt : n < 100000
    · exact h2 n hn hlt h1024
    · have hn1e5 : 100000 ≤ n := by omega
      have ho_pos : 0 < o := by omega
      have h1e5 : 2 ^ e * 100000 ^ o ≤ (3 * 100000 + 1) ^ o :=
        ratio_mono hn1e5 (by omega) hbound
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
      have hhigh : 306 * e < 485 * o := by
        have h1' : (2 ^ e * 100000 ^ o) ^ 306 ≤ ((3 * 100000 + 1) ^ o) ^ 306 :=
          Nat.pow_le_pow_left h1e5 306
        have h2' : ((3 * 100000 + 1) ^ 306) ^ o < (2 ^ 485 * 100000 ^ 306) ^ o :=
          Nat.pow_lt_pow_left upper_cutoff_pow (Nat.ne_of_gt ho_pos)
        have h3' : 2 ^ (306 * e) * 100000 ^ (306 * o) <
            2 ^ (485 * o) * 100000 ^ (306 * o) := by
          calc 2 ^ (306 * e) * 100000 ^ (306 * o)
              = (2 ^ e * 100000 ^ o) ^ 306 := by
                rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm e 306, mul_comm o 306]
            _ ≤ ((3 * 100000 + 1) ^ o) ^ 306 := h1'
            _ = ((3 * 100000 + 1) ^ 306) ^ o := by
                rw [← pow_mul, ← pow_mul, mul_comm o 306]
            _ < (2 ^ 485 * 100000 ^ 306) ^ o := h2'
            _ = 2 ^ (485 * o) * 100000 ^ (306 * o) := by
                rw [mul_pow, ← pow_mul, ← pow_mul]
        have h4' : 2 ^ (306 * e) < 2 ^ (485 * o) := Nat.lt_of_mul_lt_mul_right h3'
        exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h4'
      have hsum : e + o = k := filter_even_add_odd n k
      have ho_ge : 971 ≤ o := by omega
      have he_ge : 1539 ≤ e := by omega
      have hk_ge : 2510 ≤ k := by omega
      exact h3 n k hn1e5 h1024 hk_ge hper ho_ge he_ge hlow hhigh h32 hbound
  · exact h1 n hn h128 h1024

end OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2_H3_R1
