import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H2_R1

-- Reduction CollatzConjecture.collatz_conjecture.R1.H1.R1.H2.R1.H2.R1 of step CollatzConjecture.collatz_conjecture.R1.H1.R1.H2.R1.H2
-- Credit: @Twalways

/-!
# 10-digit continued-fraction barrier (`t >= 492531`) and mod-8192 Terras sieve for paradoxical contractions

Lifting the existential cutoff from `M >= 10^9` to `M >= 10^10` and applying the next adjacent
continued-fraction convergents of `log_2(3)`,

* lower convergent `176251 / 111202 < log_2(3)` (`2^176251 < 3^111202`),
* upper convergent `log_2(3) < 125743 / 79335` (`3^79335 < 2^125743`),
* unimodular Farey identity `111202 * 125743 - 176251 * 79335 = 1`,

together with `bernoulli_pow_bound` and `ratio_mono` from `R1.H1.R1.H2.R1`, `main` proves
directly inside Lean that every non-descending paradoxical contraction `(n, t)` with
`n >= 10^10` must satisfy:

1. **10-digit Diophantine ratio lock**: `176251 * o < 111202 * e` and `79335 * e < 125743 * o`
   (squeezing `e / o` into an interval of width `1.1 * 10^-10` around `log_2(3)`).
2. **Half-million step barrier**: `o >= 190537` odd steps, `e >= 301994` even steps, and
   `t >= 492531` total steps.

Because `t >= 492531 >= 21`, any short stopping-time descent within 21 steps contradicts
non-descent along `[0, t]`. This splits `R1.H1.R1.H2.R1.H2` cleanly into two steps:

* `H1` (finite mod-8192 Terras stopping-time sieve): every `n >= 10^10` in the 145 newly
  eliminated classes modulo 8192 (inside the 64 surviving mod-1024 classes) descends strictly
  below `n` within at most 21 steps.
* `H2` (sharpened open paradoxical obstruction): restricted to the 367 surviving classes modulo
  8192 (`4.48%` of all integers), cutoff `M >= 10^10`, `o >= 190537`, `e >= 301994`,
  `t >= 492531`, and `176251 * o < 111202 * e`, `79335 * e < 125743 * o`.
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H2_R1_H2_R1

open CollatzConjecture
open OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H2_R1

/-- Finite mod-8192 Terras stopping-time sieve: the 145 newly eliminated classes modulo 8192
inside the 64 surviving mod-1024 classes all descend strictly below `n` within 21 steps. -/
def H1 : Prop :=
  ∀ n : ℕ, 10000000000 ≤ n →
    n % 8192 ∈ ([191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159] : List ℕ) →
    ∃ s : ℕ, s ≤ 21 ∧ collatzStep^[s] n < n

/-- Sharpened paradoxical obstruction: restricted to the 367 surviving classes modulo 8192,
cutoff `M >= 10^10`, `o >= 190537`, `e >= 301994`, `t >= 492531`, and the 10-digit
continued-fraction corridor `176251 * o < 111202 * e` and `79335 * e < 125743 * o`. -/
def H2 : Prop :=
  ∃ M : ℕ, 10000000000 ≤ M ∧
    ∀ n t : ℕ, M ≤ n →
      n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495, 511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
      n % 8192 ∉ ([191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159] : List ℕ) →
      (∀ s ≤ t, n ≤ collatzStep^[s] n) →
      let e := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card
      let o := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card
      190537 ≤ o →
      301994 ≤ e →
      492531 ≤ t →
      176251 * o < 111202 * e →
      79335 * e < 125743 * o →
      3 ^ o < 2 ^ e →
      2 ^ e * n ^ o ≤ (3 * n + 1) ^ o →
      False

lemma lower_conv_10 : 2 ^ 176251 < 3 ^ 111202 := by decide +kernel

lemma upper_conv_cutoff_10 :
    3 * 10000000000 * 3 ^ 79335 < (3 * 10000000000 - 79335) * 2 ^ 125743 := by decide +kernel

lemma upper_cutoff_pow_10 :
    (3 * 10000000000 + 1) ^ 79335 < 2 ^ 125743 * 10000000000 ^ 79335 := by
  have hb := bernoulli_pow_bound (3 * 10000000000) 79335 (by omega)
  have hpow : (3 * 10000000000) ^ (79335 + 1) =
      (3 * 10000000000 * 3 ^ 79335) * 10000000000 ^ 79335 := by
    rw [pow_succ', mul_pow]
    simp only [mul_assoc]
  rw [hpow] at hb
  have hlt : (3 * 10000000000 - 79335) * (3 * 10000000000 + 1) ^ 79335 <
      (3 * 10000000000 - 79335) * (2 ^ 125743 * 10000000000 ^ 79335) := by
    calc (3 * 10000000000 - 79335) * (3 * 10000000000 + 1) ^ 79335
        ≤ (3 * 10000000000 * 3 ^ 79335) * 10000000000 ^ 79335 := hb
      _ < ((3 * 10000000000 - 79335) * 2 ^ 125743) * 10000000000 ^ 79335 :=
          Nat.mul_lt_mul_of_pos_right upper_conv_cutoff_10 (pow_pos (by omega) 79335)
      _ = (3 * 10000000000 - 79335) * (2 ^ 125743 * 10000000000 ^ 79335) := by rw [mul_assoc]
  exact Nat.lt_of_mul_lt_mul_left hlt

theorem main : H1 → H2 → OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H2_R1.H2 := by
  intro h1 h2
  rcases h2 with ⟨M, hM_ge, hM⟩
  refine ⟨M, by omega, ?_⟩
  intro n t hn h1024 hnd e o ho47 _ _ _ _ h32 hbound
  have ho_pos : 0 < o := by omega
  have h1e10 : 2 ^ e * 10000000000 ^ o ≤ (3 * 10000000000 + 1) ^ o :=
    ratio_mono (by omega) (by omega) hbound
  have hlow : 176251 * o < 111202 * e := by
    have h1' : (2 ^ 176251) ^ o < (3 ^ 111202) ^ o :=
      Nat.pow_lt_pow_left lower_conv_10 (Nat.ne_of_gt ho_pos)
    have h2' : (3 ^ o) ^ 111202 < (2 ^ e) ^ 111202 :=
      Nat.pow_lt_pow_left h32 (by decide)
    have h3' : 2 ^ (176251 * o) < 2 ^ (111202 * e) := by
      calc 2 ^ (176251 * o) = (2 ^ 176251) ^ o := pow_mul 2 176251 o
        _ < (3 ^ 111202) ^ o := h1'
        _ = 3 ^ (111202 * o) := (pow_mul 3 111202 o).symm
        _ = 3 ^ (o * 111202) := by rw [mul_comm]
        _ = (3 ^ o) ^ 111202 := pow_mul 3 o 111202
        _ < (2 ^ e) ^ 111202 := h2'
        _ = 2 ^ (e * 111202) := (pow_mul 2 e 111202).symm
        _ = 2 ^ (111202 * e) := by rw [mul_comm]
    exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h3'
  have hhigh : 79335 * e < 125743 * o := by
    have h1' : (2 ^ e * 10000000000 ^ o) ^ 79335 ≤ ((3 * 10000000000 + 1) ^ o) ^ 79335 :=
      Nat.pow_le_pow_left h1e10 79335
    have h2' : ((3 * 10000000000 + 1) ^ 79335) ^ o <
        (2 ^ 125743 * 10000000000 ^ 79335) ^ o :=
      Nat.pow_lt_pow_left upper_cutoff_pow_10 (Nat.ne_of_gt ho_pos)
    have h3' : 2 ^ (79335 * e) * 10000000000 ^ (79335 * o) <
        2 ^ (125743 * o) * 10000000000 ^ (79335 * o) := by
      calc 2 ^ (79335 * e) * 10000000000 ^ (79335 * o)
          = (2 ^ e * 10000000000 ^ o) ^ 79335 := by
            rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm e 79335, mul_comm o 79335]
        _ ≤ ((3 * 10000000000 + 1) ^ o) ^ 79335 := h1'
        _ = ((3 * 10000000000 + 1) ^ 79335) ^ o := by
            rw [← pow_mul, ← pow_mul, mul_comm o 79335]
        _ < (2 ^ 125743 * 10000000000 ^ 79335) ^ o := h2'
        _ = 2 ^ (125743 * o) * 10000000000 ^ (79335 * o) := by
            rw [mul_pow, ← pow_mul, ← pow_mul]
    have h4' : 2 ^ (79335 * e) < 2 ^ (125743 * o) := Nat.lt_of_mul_lt_mul_right h3'
    exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h4'
  have hsum : e + o = t := filter_even_add_odd n t
  have ho_ge : 190537 ≤ o := by omega
  have he_ge : 301994 ≤ e := by omega
  have ht_ge : 492531 ≤ t := by omega
  by_cases h8192 : n % 8192 ∈ ([191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159] : List ℕ)
  · obtain ⟨s, hs21, hslt⟩ := h1 n (by omega) h8192
    have hge := hnd s (by omega)
    omega
  · exact hM n t hn h1024 h8192 hnd ho_ge he_ge ht_ge hlow hhigh h32 hbound

end OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H2_R1_H2_R1
