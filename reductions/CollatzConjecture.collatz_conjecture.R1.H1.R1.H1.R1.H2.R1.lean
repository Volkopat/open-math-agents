import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1

-- Reduction CollatzConjecture.collatz_conjecture.R1.H1.R1.H1.R1.H2.R1 of step CollatzConjecture.collatz_conjecture.R1.H1.R1.H1.R1.H2
-- Credit: @Twalways

/-!
# Mod-8192 Terras sieve and 6-digit global linear density corridor (`306 * t < 791 * o`)

Using the all-`k` Terras cylinder hypothesis of `R1.H1.R1.H1.R1.H2` together with
`terras_invariance_aux` and `even_add_odd_card` from `R1.H1.R1.H1.R1`, `main` proves directly
inside Lean:

1. **Global non-contraction along `n`**: instantiating the Terras cylinder at `k = t + 1` gives
   `2 ^ e(n, t) <= 3 ^ o(n, t)` for every `t : ℕ`.
2. **6-digit global linear odd-density corridor**: since `3 ^ 306 < 2 ^ 485`, every `t > 0`
   satisfies `306 * t < 791 * o(n, t)` and `791 * e(n, t) < 485 * t`
   (`306 / 791 = 0.386852...`, sharpening `5 / 13 = 0.384615...` to 6 decimal places of
   `1 / (1 + log_2(3))`).
3. **Mod-8192 Terras sieve**: instantiating `k = 13` (`2^13 = 8192`) eliminates 145 additional
   classes inside `surv64`, cutting overall density to `367 / 8192 = 4.48%`.

This splits `R1.H1.R1.H1.R1.H2` cleanly into two steps:

* `H1` (finite mod-8192 Terras check, 145 residues): every `r` in the 145 eliminated mod-8192
  classes contracts (`e <= 13` and `3 ^ o < 2 ^ e`) within 21 steps.
* `H2` (sharpened open core): restricted to the 367 surviving mod-8192 classes with the
  6-digit linear corridor `306 * t < 791 * o` and `791 * e < 485 * t` for all `t > 0`.
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1_H2_R1

open CollatzConjecture
open OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1
open OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1

/-- Finite mod-8192 Terras sieve: every residue `r` in the 145 eliminated mod-8192 classes
contracts (`e <= 13` and `3 ^ o < 2 ^ e`) within 21 steps. -/
def H1 : Prop :=
  ∀ r : ℕ, r ∈ ([191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159] : List ℕ) →
    ∃ t : ℕ, t ≤ 21 ∧
      ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 0)).card ≤ 13 ∧
      3 ^ ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 1)).card <
      2 ^ ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 0)).card

/-- Sharpened open core: no never-descending divergent `n >= 10000` in the 367 surviving
mod-8192 classes stays in every Terras cylinder while satisfying the 6-digit linear density
corridor `306 * t < 791 * o`, `791 * e < 485 * t`, and `o <= e + 1` for every `t > 0`. -/
def H2 : Prop :=
  ∀ n : ℕ, 10000 ≤ n →
    n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495, 511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    n % 8192 ∉ ([191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159] : List ℕ) →
    (∀ t : ℕ, n ≤ collatzStep^[t] n) →
    (∀ B : ℕ, ∃ t : ℕ, B < collatzStep^[t] n) →
    (∀ k t : ℕ,
      ((Finset.range t).filter (fun i => collatzStep^[i] (n % 2 ^ k) % 2 = 0)).card ≤ k →
      2 ^ ((Finset.range t).filter (fun i => collatzStep^[i] (n % 2 ^ k) % 2 = 0)).card ≤
      3 ^ ((Finset.range t).filter (fun i => collatzStep^[i] (n % 2 ^ k) % 2 = 1)).card) →
    (∀ t : ℕ, 0 < t →
      let e := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card
      let o := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card
      306 * t < 791 * o ∧ 791 * e < 485 * t ∧ o ≤ e + 1) →
    False

lemma pow_306_lt_485 : (3 : ℕ) ^ 306 < 2 ^ 485 := by decide +kernel

lemma card_filter_range_le (r i : ℕ) :
    ((Finset.range i).filter (fun j => collatzStep^[j] r % 2 = 0)).card ≤ i := by
  calc ((Finset.range i).filter (fun j => collatzStep^[j] r % 2 = 0)).card
      ≤ (Finset.range i).card := Finset.card_filter_le _ _
    _ = i := Finset.card_range i

theorem main : H1 → H2 → OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1.H2 := by
  intro h1 h2 n hn h1024 hmin hunb hcyl hlin
  by_cases h8192 : n % 8192 ∈ ([191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159] : List ℕ)
  · obtain ⟨t, _, he13, h32⟩ := h1 (n % 8192) h8192
    have hpow : (2 : ℕ) ^ 13 = 8192 := by norm_num
    have h13 := hcyl 13 t (by rw [hpow]; exact he13)
    rw [hpow] at h13
    omega
  · apply h2 n hn h1024 h8192 hmin hunb hcyl
    intro t ht
    have hlin_t := hlin t ht
    dsimp only at hlin_t ⊢
    set e := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card
    set o := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card
    have heo : e + o = t := even_add_odd_card n t
    have ho_pos : 0 < o := by omega
    set k := t + 1
    set r := n % 2 ^ k
    have he_all : ∀ i < t, ((Finset.range i).filter (fun j => collatzStep^[j] r % 2 = 0)).card < k := by
      intro i hi
      exact lt_of_le_of_lt (card_filter_range_le r i) (by omega)
    have hmod : n % 2 ^ k = r % 2 ^ k := by
      dsimp [r]
      rw [Nat.mod_mod]
    obtain ⟨_, he_eq, ho_eq⟩ := terras_invariance_aux n r k t hmod he_all
    have hr_le : ((Finset.range t).filter (fun j => collatzStep^[j] r % 2 = 0)).card ≤ k :=
      le_trans (card_filter_range_le r t) (by omega)
    have hnc_r := hcyl k t hr_le
    have hnc : 2 ^ e ≤ 3 ^ o := by
      dsimp [e, o]
      rw [he_eq, ho_eq]
      exact hnc_r
    have h306 : (2 ^ e) ^ 306 ≤ (3 ^ o) ^ 306 := Nat.pow_le_pow_left hnc 306
    have hpow_lt : (3 ^ 306) ^ o < (2 ^ 485) ^ o :=
      Nat.pow_lt_pow_left pow_306_lt_485 (Nat.ne_of_gt ho_pos)
    have h2lt : 2 ^ (306 * e) < 2 ^ (485 * o) := by
      calc 2 ^ (306 * e) = (2 ^ e) ^ 306 := by rw [← pow_mul, mul_comm]
        _ ≤ (3 ^ o) ^ 306 := h306
        _ = (3 ^ 306) ^ o := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ < (2 ^ 485) ^ o := hpow_lt
        _ = 2 ^ (485 * o) := by rw [← pow_mul]
    have hsharp : 306 * e < 485 * o :=
      (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h2lt
    exact ⟨by omega, by omega, hlin_t.2.2⟩

end OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1_H2_R1
