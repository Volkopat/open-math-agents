import OMAReductions.R_CollatzConjecture_collatz_conjecture_R2_H2_R1

-- Reduction CollatzConjecture.collatz_conjecture.R2.H2.R1.H3.R1 of step CollatzConjecture.collatz_conjecture.R2.H2.R1.H3
-- Credit: @Twalways

/-!
# Mod-8192 Terras sieve (`2.99%` density) and 5x cutoff lift (`10000 -> 50000`) for R2.H2.R1.H3

Reusing `terras_invariance`, `even_count_mono`, and `ratio_of_reaches_one` from `R2.H2.R1`,
`main` lifts the Terras modular-invariance sieve to modulo `8192 = 2^13` (eliminating 145
additional classes out of 512 inside `surv64`, cutting remaining density by 28.3% down to
`734/24576 ≈ 2.99%` of all integers) and lifts the cutoff 5x from `10000` to `50000`.

This splits `R2.H2.R1.H3` cleanly into three steps:

* `H1` (finite mod-8192 Terras check, 145 residues): every `r` in the 145 eliminated mod-8192
  classes achieves `e <= 13` and `3001 ^ o < 2 ^ e * 1000 ^ o` within 21 steps.
* `H2` (finite base check, 1192 integers): every `10000 <= n < 50000` in the 367 surviving
  mod-8192 classes with `n % 3 != 2` reaches `1`.
* `H3` (sharpened open core): symbolic halving-ratio contraction `3001 ^ o < 2 ^ e * 1000 ^ o`
  restricted to `n >= 50000`, the 367 surviving mod-8192 classes, and `n % 3 != 2`.
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R2_H2_R1_H3_R1

open CollatzConjecture
open OMA.R_CollatzConjecture_collatz_conjecture_R2
open OMA.R_CollatzConjecture_collatz_conjecture_R2_H2_R1

/-- Finite mod-8192 Terras contraction sieve: the 145 newly eliminated classes modulo 8192
inside the 64 surviving mod-1024 classes all satisfy `e <= 13` and
`3001 ^ o < 2 ^ e * 1000 ^ o` within 21 steps. -/
def H1 : Prop :=
  ∀ r : ℕ, r ∈ ([191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159] : List ℕ) →
    ∃ m : ℕ, m ≤ 21 ∧
      let e := ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 0)).card
      let o := ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 1)).card
      e ≤ 13 ∧ 3001 ^ o < 2 ^ e * 1000 ^ o

/-- Finite base check on `[10000, 50000)`: every integer in the 367 surviving mod-8192 classes
with `n % 3 != 2` (1192 integers total; max steps to 1 is 323) reaches `1`. -/
def H2 : Prop :=
  ∀ n : ℕ, 10000 ≤ n → n < 50000 →
    n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495, 511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    n % 8192 ∉ ([191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159] : List ℕ) →
    n % 3 ≠ 2 →
    ∃ t : ℕ, collatzStep^[t] n = 1

/-- Sharpened open core: every `n >= 50000` in the 367 surviving mod-8192 classes with
`n % 3 != 2` (2.99% of all integers) eventually satisfies `3001 ^ o < 2 ^ e * 1000 ^ o`. -/
def H3 : Prop :=
  ∀ n : ℕ, 50000 ≤ n →
    n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495, 511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    n % 8192 ∉ ([191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159] : List ℕ) →
    n % 3 ≠ 2 →
    ∃ m : ℕ,
      let e := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card
      let o := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card
      3001 ^ o < 2 ^ e * 1000 ^ o

theorem main : H1 → H2 → H3 → OMA.R_CollatzConjecture_collatz_conjecture_R2_H2_R1.H3 := by
  intro h1 h2 h3 n hn h1024 hmod3
  by_cases h8192 : n % 8192 ∈ ([191, 207, 231, 255, 303, 383, 463, 539, 543, 615, 623, 679, 719, 799, 879, 935, 1019, 1071, 1087, 1135, 1191, 1215, 1231, 1247, 1327, 1435, 1563, 1567, 1647, 1703, 1727, 1787, 1823, 1855, 1983, 2015, 2031, 2075, 2079, 2095, 2203, 2239, 2271, 2331, 2351, 2431, 2587, 2591, 2607, 2663, 2907, 2975, 3039, 3067, 3119, 3135, 3143, 3295, 3455, 3483, 3551, 3559, 3675, 3687, 3835, 3903, 3911, 3967, 4063, 4079, 4091, 4159, 4199, 4223, 4251, 4327, 4455, 4479, 4507, 4559, 4711, 4859, 4927, 4955, 4975, 5023, 5031, 5103, 5115, 5183, 5191, 5275, 5327, 5371, 5439, 5531, 5607, 5615, 5723, 5743, 5787, 5799, 5871, 5883, 5919, 5951, 5959, 5979, 6047, 6127, 6215, 6299, 6335, 6375, 6447, 6559, 6607, 6631, 6683, 6687, 6747, 6815, 6983, 7003, 7023, 7071, 7079, 7215, 7239, 7259, 7375, 7391, 7399, 7495, 7631, 7655, 7771, 7791, 7847, 7911, 7967, 8007, 8047, 8103, 8159] : List ℕ)
  · set r := n % 8192
    obtain ⟨m0, _, he0, hratio0⟩ := h1 r h8192
    classical
    have hex : ∃ m : ℕ,
        3001 ^ ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 1)).card <
        2 ^ ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 0)).card *
        1000 ^ ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 1)).card :=
      ⟨m0, hratio0⟩
    set m := Nat.find hex
    have hm_spec :
        3001 ^ ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 1)).card <
        2 ^ ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 0)).card *
        1000 ^ ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 1)).card :=
      Nat.find_spec hex
    have hm_le : m ≤ m0 := Nat.find_min' hex hratio0
    have hem_le : ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 0)).card ≤ 13 :=
      le_trans (even_count_mono r hm_le) he0
    have hm_pos : 0 < m := by
      by_contra h0
      have hm0' : m = 0 := by omega
      rw [hm0'] at hm_spec
      simp at hm_spec
    set k := m - 1
    have hmk : m = k + 1 := by omega
    have hlast_even : collatzStep^[k] r % 2 = 0 := by
      by_contra hne
      have hk1 : collatzStep^[k] r % 2 = 1 := by omega
      have hni1 : k ∉ (Finset.range k).filter (fun i => collatzStep^[i] r % 2 = 1) := by simp
      have he_eq : ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 0)).card =
          ((Finset.range k).filter (fun i => collatzStep^[i] r % 2 = 0)).card := by
        rw [hmk, Finset.range_add_one, Finset.filter_insert]
        simp [hne]
      have ho_eq : ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 1)).card =
          ((Finset.range k).filter (fun i => collatzStep^[i] r % 2 = 1)).card + 1 := by
        rw [hmk, Finset.range_add_one, Finset.filter_insert]
        simp [hk1, Finset.card_insert_of_notMem hni1]
      rw [he_eq, ho_eq] at hm_spec
      set ek := ((Finset.range k).filter (fun i => collatzStep^[i] r % 2 = 0)).card
      set ok := ((Finset.range k).filter (fun i => collatzStep^[i] r % 2 = 1)).card
      have hprev : 3001 ^ ok < 2 ^ ek * 1000 ^ ok := by
        have h1' : 1000 * 3001 ^ ok < 3001 * 3001 ^ ok :=
          Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos (by omega) ok)
        have h2' : 3001 * 3001 ^ ok = 3001 ^ (ok + 1) := (pow_succ' 3001 ok).symm
        have h3' : 2 ^ ek * 1000 ^ (ok + 1) = 1000 * (2 ^ ek * 1000 ^ ok) := by
          rw [pow_succ']
          ring
        have h4' : 1000 * 3001 ^ ok < 1000 * (2 ^ ek * 1000 ^ ok) := by omega
        exact Nat.lt_of_mul_lt_mul_left h4'
      exact Nat.find_min hex (by omega : k < m) hprev
    have hek_lt : ((Finset.range k).filter (fun i => collatzStep^[i] r % 2 = 0)).card < 13 := by
      have hni0 : k ∉ (Finset.range k).filter (fun i => collatzStep^[i] r % 2 = 0) := by simp
      have he_succ : ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 0)).card =
          ((Finset.range k).filter (fun i => collatzStep^[i] r % 2 = 0)).card + 1 := by
        rw [hmk, Finset.range_add_one, Finset.filter_insert]
        simp [hlast_even, Finset.card_insert_of_notMem hni0]
      omega
    have hlt_all : ∀ i < m, ((Finset.range i).filter (fun j => collatzStep^[j] r % 2 = 0)).card < 13 := by
      intro i hi
      exact lt_of_le_of_lt (even_count_mono r (by omega : i ≤ k)) hek_lt
    have hmod_nr : n % 2 ^ 13 = r % 2 ^ 13 := by
      show n % 8192 = (n % 8192) % 8192
      rw [Nat.mod_mod]
    have hpar := (terras_invariance n r m 13 hmod_nr hlt_all).2
    have hfe : (Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0) =
        (Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 0) := by
      apply Finset.filter_congr
      intro i hi
      rw [hpar i (Finset.mem_range.mp hi)]
    have hfo : (Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1) =
        (Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 1) := by
      apply Finset.filter_congr
      intro i hi
      rw [hpar i (Finset.mem_range.mp hi)]
    refine ⟨m, ?_⟩
    dsimp only
    rw [hfe, hfo]
    exact hm_spec
  · by_cases hlt : n < 50000
    · obtain ⟨t, ht⟩ := h2 n hn hlt h1024 h8192 hmod3
      exact ratio_of_reaches_one ht
    · exact h3 n (by omega) h1024 h8192 hmod3

end OMA.R_CollatzConjecture_collatz_conjecture_R2_H2_R1_H3_R1
