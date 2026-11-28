import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H1_R1

-- Reduction CollatzConjecture.collatz_conjecture.R1.H1.R1.H2.R1 of step CollatzConjecture.collatz_conjecture.R1.H1.R1.H2
-- Credit: @Twalways

/-!
# Continued-fraction Diophantine barrier and mod-1024 Terras sieve for paradoxical contractions

Because `CollatzConjecture.collatz_conjecture.R1.H1.R1.H2` asks for an existential cutoff
`M >= 10000`, any larger cutoff may be chosen without finite base verification. Taking
`M >= 10^9` and applying adjacent continued-fraction convergents of `log_2(3)`,

* lower convergent `50508 / 31867 < log_2(3)` (`2^50508 < 3^31867`),
* upper convergent `log_2(3) < 24727 / 15601` (`3^15601 < 2^24727`),
* unimodular Farey identity `31867 * 24727 - 50508 * 15601 = 1`,

together with the elementary induction inequality `(x - d) * (x + 1)^d <= x^(d + 1)`, `main`
proves directly inside Lean that every non-descending paradoxical contraction `(n, t)` with
`n >= 10^9` must satisfy:

1. **8-digit Diophantine ratio lock**: `50508 * o < 31867 * e` and `15601 * e < 24727 * o`
   (squeezing `e / o` into an interval of width `3 * 10^-9` around `log_2(3)`).
2. **Large length barrier**: `o >= 47468` odd steps, `e >= 75235` even steps, and
   `t >= 122703` total steps.

Because `t >= 122703 >= 16`, any short stopping-time descent within 16 steps contradicts
non-descent along `[0, t]`. This splits `R1.H1.R1.H2` cleanly into two steps:

* `H1` (finite mod-1024 Terras stopping-time sieve): every `n >= 10^9` in the 40 eliminated
  classes modulo 1024 (inside the 13 mod-128 classes, outside the 64 surviving mod-1024 classes)
  descends strictly below `n` within at most 16 steps.
* `H2` (sharpened open paradoxical obstruction): restricted to the 64 surviving residue classes
  modulo 1024, cutoff `M >= 10^9`, `o >= 47468`, `e >= 75235`, `t >= 122703`, and the
  8-digit continued-fraction corridor `50508 * o < 31867 * e` and `15601 * e < 24727 * o`.
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H2_R1

open CollatzConjecture

/-- Finite mod-1024 Terras stopping-time sieve: the 40 eliminated residue classes modulo 1024
within the 13 surviving mod-128 classes all descend strictly below `n` in at most 16 steps
for every `n >= 10^9`. -/
def H1 : Prop :=
  ∀ n : ℕ, 1000000000 ≤ n →
    (n % 128 = 27 ∨ n % 128 = 31 ∨ n % 128 = 39 ∨ n % 128 = 47 ∨
     n % 128 = 63 ∨ n % 128 = 71 ∨ n % 128 = 79 ∨ n % 128 = 91 ∨
     n % 128 = 95 ∨ n % 128 = 103 ∨ n % 128 = 111 ∨ n % 128 = 123 ∨ n % 128 = 127) →
    n % 1024 ∉ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
      239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
      767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    ∃ s : ℕ, s ≤ 16 ∧ collatzStep^[s] n < n

/-- Sharpened paradoxical non-descending contraction obstruction: restricted to the 64 surviving
residue classes modulo 1024, cutoff `M >= 10^9`, `o >= 47468`, `e >= 75235`, `t >= 122703`,
and the continued-fraction corridor `50508 * o < 31867 * e` and `15601 * e < 24727 * o`. -/
def H2 : Prop :=
  ∃ M : ℕ, 1000000000 ≤ M ∧
    ∀ n t : ℕ, M ≤ n →
      n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
        239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
        511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
        767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
      (∀ s ≤ t, n ≤ collatzStep^[s] n) →
      let e := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card
      let o := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card
      47468 ≤ o →
      75235 ≤ e →
      122703 ≤ t →
      50508 * o < 31867 * e →
      15601 * e < 24727 * o →
      3 ^ o < 2 ^ e →
      2 ^ e * n ^ o ≤ (3 * n + 1) ^ o →
      False

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

lemma lower_conv : 2 ^ 50508 < 3 ^ 31867 := by decide +kernel

lemma upper_conv_cutoff :
    3 * 1000000000 * 3 ^ 15601 < (3 * 1000000000 - 15601) * 2 ^ 24727 := by decide +kernel

lemma upper_cutoff_pow :
    (3 * 1000000000 + 1) ^ 15601 < 2 ^ 24727 * 1000000000 ^ 15601 := by
  have hb := bernoulli_pow_bound (3 * 1000000000) 15601 (by omega)
  have hpow : (3 * 1000000000) ^ (15601 + 1) =
      (3 * 1000000000 * 3 ^ 15601) * 1000000000 ^ 15601 := by
    rw [pow_succ', mul_pow]
    simp only [mul_assoc]
  rw [hpow] at hb
  have hlt : (3 * 1000000000 - 15601) * (3 * 1000000000 + 1) ^ 15601 <
      (3 * 1000000000 - 15601) * (2 ^ 24727 * 1000000000 ^ 15601) := by
    calc (3 * 1000000000 - 15601) * (3 * 1000000000 + 1) ^ 15601
        ≤ (3 * 1000000000 * 3 ^ 15601) * 1000000000 ^ 15601 := hb
      _ < ((3 * 1000000000 - 15601) * 2 ^ 24727) * 1000000000 ^ 15601 :=
          Nat.mul_lt_mul_of_pos_right upper_conv_cutoff (pow_pos (by omega) 15601)
      _ = (3 * 1000000000 - 15601) * (2 ^ 24727 * 1000000000 ^ 15601) := by rw [mul_assoc]
  exact Nat.lt_of_mul_lt_mul_left hlt

lemma filter_even_add_odd (n : ℕ) : ∀ t : ℕ,
    ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card +
    ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card = t
  | 0 => by simp
  | t + 1 => by
    rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    have hni : t ∉ Finset.range t := by simp
    have ih := filter_even_add_odd n t
    by_cases h : collatzStep^[t] n % 2 = 0
    · have hni0 : t ∉ (Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0) := by
        simp [hni]
      simp [h, Finset.card_insert_of_notMem hni0]
      omega
    · have h1 : collatzStep^[t] n % 2 = 1 := by omega
      have hni1 : t ∉ (Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1) := by
        simp [hni]
      simp [h1, Finset.card_insert_of_notMem hni1]
      omega

theorem main : H1 → H2 → OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1.H2 := by
  intro h1 h2
  rcases h2 with ⟨M, hM_ge, hM⟩
  refine ⟨M, by omega, ?_⟩
  intro n t hn h128 hnd e o h32 hbound
  have ho_pos : 0 < o := by
    by_contra h0
    have ho0 : o = 0 := by omega
    simp only [ho0, pow_zero, mul_one] at h32 hbound
    omega
  have h1e9 : 2 ^ e * 1000000000 ^ o ≤ (3 * 1000000000 + 1) ^ o :=
    ratio_mono (by omega) (by omega) hbound
  have hlow : 50508 * o < 31867 * e := by
    have h1' : (2 ^ 50508) ^ o < (3 ^ 31867) ^ o :=
      Nat.pow_lt_pow_left lower_conv (Nat.ne_of_gt ho_pos)
    have h2' : (3 ^ o) ^ 31867 < (2 ^ e) ^ 31867 :=
      Nat.pow_lt_pow_left h32 (by decide)
    have h3' : 2 ^ (50508 * o) < 2 ^ (31867 * e) := by
      calc 2 ^ (50508 * o) = (2 ^ 50508) ^ o := pow_mul 2 50508 o
        _ < (3 ^ 31867) ^ o := h1'
        _ = 3 ^ (31867 * o) := (pow_mul 3 31867 o).symm
        _ = 3 ^ (o * 31867) := by rw [mul_comm]
        _ = (3 ^ o) ^ 31867 := pow_mul 3 o 31867
        _ < (2 ^ e) ^ 31867 := h2'
        _ = 2 ^ (e * 31867) := (pow_mul 2 e 31867).symm
        _ = 2 ^ (31867 * e) := by rw [mul_comm]
    exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h3'
  have hhigh : 15601 * e < 24727 * o := by
    have h1' : (2 ^ e * 1000000000 ^ o) ^ 15601 ≤ ((3 * 1000000000 + 1) ^ o) ^ 15601 :=
      Nat.pow_le_pow_left h1e9 15601
    have h2' : ((3 * 1000000000 + 1) ^ 15601) ^ o <
        (2 ^ 24727 * 1000000000 ^ 15601) ^ o :=
      Nat.pow_lt_pow_left upper_cutoff_pow (Nat.ne_of_gt ho_pos)
    have h3' : 2 ^ (15601 * e) * 1000000000 ^ (15601 * o) <
        2 ^ (24727 * o) * 1000000000 ^ (15601 * o) := by
      calc 2 ^ (15601 * e) * 1000000000 ^ (15601 * o)
          = (2 ^ e * 1000000000 ^ o) ^ 15601 := by
            rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm e 15601, mul_comm o 15601]
        _ ≤ ((3 * 1000000000 + 1) ^ o) ^ 15601 := h1'
        _ = ((3 * 1000000000 + 1) ^ 15601) ^ o := by
            rw [← pow_mul, ← pow_mul, mul_comm o 15601]
        _ < (2 ^ 24727 * 1000000000 ^ 15601) ^ o := h2'
        _ = 2 ^ (24727 * o) * 1000000000 ^ (15601 * o) := by
            rw [mul_pow, ← pow_mul, ← pow_mul]
    have h4' : 2 ^ (15601 * e) < 2 ^ (24727 * o) := Nat.lt_of_mul_lt_mul_right h3'
    exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h4'
  have hsum : e + o = t := filter_even_add_odd n t
  have ho_ge : 47468 ≤ o := by omega
  have he_ge : 75235 ≤ e := by omega
  have ht_ge : 122703 ≤ t := by omega
  by_cases h1024 : n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207,
      223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795,
      799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ)
  · exact hM n t hn h1024 hnd ho_ge he_ge ht_ge hlow hhigh h32 hbound
  · obtain ⟨s, hs16, hslt⟩ := h1 n (by omega) h128 h1024
    have hge := hnd s (by omega)
    omega

end OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H2_R1
