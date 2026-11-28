import OMAReductions.R_CollatzConjecture_collatz_conjecture_R2

-- Reduction CollatzConjecture.collatz_conjecture.R2.H2.R1 of step CollatzConjecture.collatz_conjecture.R2.H2
-- Credit: @Twalways

/-!
# Mod-1024 Terras modular-invariance sieve and 1-cycle cutoff lift for R2.H2

`main` proves two general structural theorems directly inside Lean:

1. **Terras (1976) Modular Invariance Theorem**: whenever `n % 2 ^ k = r % 2 ^ k` and the
   even-step count satisfies `e(r, i) < k` for every `i < m`, the Collatz parity vectors of
   `n` and `r` coincide on `[0, m)`. Moreover, at the minimal contraction index `m'` where
   `3001 ^ o < 2 ^ e * 1000 ^ o` first holds, the last step `m' - 1` must be even, so
   `e(r, m') <= 10` automatically guarantees `e(r, i) < 10` for every `i < m'`. This eliminates
   exactly half (64 of 128) of the mod-1024 classes inside `{7, 15, 27, 31} mod 32`.
2. **1-Cycle Ratio Amplification Lemma**: any integer `n` whose trajectory reaches `1`
   eventually satisfies `3001 ^ o < 2 ^ e * 1000 ^ o`, proved by looping around `1 -> 4 -> 2 -> 1`
   (which adds 2 even steps and 1 odd step per 3 steps, using `3001 ^ 5 < 1000 * 4000 ^ 4`).

This splits `R2.H2` cleanly into three steps:

* `H1` (finite mod-1024 Terras check, 64 residues): every residue `r < 1024` in
  `{7, 15, 27, 31} mod 32` outside the 64 surviving mod-1024 classes achieves
  `e <= 10` and `3001 ^ o < 2 ^ e * 1000 ^ o` within at most 16 steps.
* `H2` (finite base check, 375 integers): every `1000 <= n < 10000` in the 64 surviving
  mod-1024 classes with `n % 3 != 2` reaches `1`.
* `H3` (sharpened open core): symbolic halving-ratio contraction `3001 ^ o < 2 ^ e * 1000 ^ o`
  restricted to `n >= 10000`, the 64 surviving mod-1024 classes, and `n % 3 != 2`
  (cutting density by 50% from `8/96` to `128/3072` and lifting the cutoff 10x to `10000`).
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R2_H2_R1

open CollatzConjecture
open OMA.R_CollatzConjecture_collatz_conjecture_R2

/-- Finite mod-1024 Terras contraction sieve: the 64 eliminated classes modulo 1024 inside
`{7, 15, 27, 31} mod 32` all satisfy `e <= 10` and `3001 ^ o < 2 ^ e * 1000 ^ o` within 16 steps. -/
def H1 : Prop :=
  ∀ r : ℕ, r < 1024 →
    (r % 32 = 7 ∨ r % 32 = 15 ∨ r % 32 = 27 ∨ r % 32 = 31) →
    r ∉ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
      239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
      767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    ∃ m : ℕ, m ≤ 16 ∧
      let e := ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 0)).card
      let o := ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 1)).card
      e ≤ 10 ∧ 3001 ^ o < 2 ^ e * 1000 ^ o

/-- Finite base check on `[1000, 10000)`: every integer in the 64 surviving mod-1024 classes
with `n % 3 != 2` (375 integers total) reaches `1`. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000 ≤ n → n < 10000 →
    n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
      239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
      767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    n % 3 ≠ 2 →
    ∃ t : ℕ, collatzStep^[t] n = 1

/-- Sharpened open core: every `n >= 10000` in the 64 surviving mod-1024 classes with
`n % 3 != 2` eventually reaches a prefix with `3001 ^ o < 2 ^ e * 1000 ^ o`. -/
def H3 : Prop :=
  ∀ n : ℕ, 10000 ≤ n →
    n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
      239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
      767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    n % 3 ≠ 2 →
    ∃ m : ℕ,
      let e := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card
      let o := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card
      3001 ^ o < 2 ^ e * 1000 ^ o

lemma div2_mod_eq {a b d : ℕ} (h : a % (2 * d) = b % (2 * d)) :
    (a / 2) % d = (b / 2) % d := by
  have ha : a / 2 = d * (a / (2 * d)) + (a % (2 * d)) / 2 := by
    have h1 : a = 2 * d * (a / (2 * d)) + a % (2 * d) := (Nat.div_add_mod a (2 * d)).symm
    have h2 : 2 * d * (a / (2 * d)) = 2 * (d * (a / (2 * d))) := by ring
    omega
  have hb : b / 2 = d * (b / (2 * d)) + (b % (2 * d)) / 2 := by
    have h1 : b = 2 * d * (b / (2 * d)) + b % (2 * d) := (Nat.div_add_mod b (2 * d)).symm
    have h2 : 2 * d * (b / (2 * d)) = 2 * (d * (b / (2 * d))) := by ring
    omega
  rw [ha, hb, h, Nat.mul_add_mod, Nat.mul_add_mod]

lemma mod2_eq_of_mod_pow {a b j : ℕ} (hj : 0 < j) (h : a % 2 ^ j = b % 2 ^ j) :
    a % 2 = b % 2 := by
  have hdvd : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
  rw [← Nat.mod_mod_of_dvd a hdvd, h, Nat.mod_mod_of_dvd b hdvd]

lemma mul3_add1_mod_eq {a b d : ℕ} (h : a % d = b % d) :
    (3 * a + 1) % d = (3 * b + 1) % d := by
  rw [Nat.add_mod, Nat.mul_mod, h, ← Nat.mul_mod, ← Nat.add_mod]

lemma even_count_mono (r : ℕ) {i j : ℕ} (hij : i ≤ j) :
    ((Finset.range i).filter (fun s => collatzStep^[s] r % 2 = 0)).card ≤
    ((Finset.range j).filter (fun s => collatzStep^[s] r % 2 = 0)).card :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))

lemma terras_invariance (n r : ℕ) : ∀ m k : ℕ,
    n % 2 ^ k = r % 2 ^ k →
    (∀ i < m, ((Finset.range i).filter (fun j => collatzStep^[j] r % 2 = 0)).card < k) →
    (collatzStep^[m] n) % 2 ^ (k - ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 0)).card) =
    (collatzStep^[m] r) % 2 ^ (k - ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 0)).card) ∧
    ∀ i < m, collatzStep^[i] n % 2 = collatzStep^[i] r % 2
  | 0, k, hmod, _ => by
    refine ⟨by simpa using hmod, ?_⟩
    intro i hi
    omega
  | m + 1, k, hmod, hlt => by
    obtain ⟨hih_mod, hih_par⟩ := terras_invariance n r m k hmod (fun i hi => hlt i (by omega))
    have he_lt : ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 0)).card < k :=
      hlt m (by omega)
    have hpar_m : collatzStep^[m] n % 2 = collatzStep^[m] r % 2 :=
      mod2_eq_of_mod_pow (by omega) hih_mod
    have hni : m ∉ (Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 0) := by simp
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Finset.range_add_one, Finset.filter_insert]
      by_cases hr0 : collatzStep^[m] r % 2 = 0
      · have hn0 : collatzStep^[m] n % 2 = 0 := by omega
        rw [collatzStep_even hn0, collatzStep_even hr0]
        simp only [hr0, ↓reduceIte, Finset.card_insert_of_notMem hni]
        set em := ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 0)).card
        have hpow : 2 ^ (k - em) = 2 * 2 ^ (k - (em + 1)) := by
          have hexp : k - em = (k - (em + 1)) + 1 := by omega
          rw [hexp, pow_succ']
        rw [hpow] at hih_mod
        exact div2_mod_eq hih_mod
      · have hr1 : collatzStep^[m] r % 2 = 1 := by omega
        have hn1 : collatzStep^[m] n % 2 = 1 := by omega
        rw [collatzStep_odd hn1, collatzStep_odd hr1]
        simp only [hr0, ↓reduceIte]
        exact mul3_add1_mod_eq hih_mod
    · intro i hi
      by_cases him : i < m
      · exact hih_par i him
      · have hieq : i = m := by omega
        rw [hieq]
        exact hpar_m

lemma collatzStep_one : collatzStep 1 = 4 := by
  rw [collatzStep_odd (by omega)]

lemma collatzStep_four : collatzStep 4 = 2 := by
  rw [collatzStep_even (by omega)]

lemma collatzStep_two : collatzStep 2 = 1 := by
  rw [collatzStep_even (by omega)]

lemma iter_three_one : ∀ r : ℕ, collatzStep^[3 * r] 1 = 1
  | 0 => by simp
  | r + 1 => by
    rw [show 3 * (r + 1) = 3 + 3 * r by omega, Function.iterate_add_apply, iter_three_one r]
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq,
      collatzStep_one, collatzStep_four, collatzStep_two]

lemma even_odd_add_three_one {n t : ℕ} (ht : collatzStep^[t] n = 1) : ∀ r : ℕ,
    ((Finset.range (t + 3 * r)).filter (fun i => collatzStep^[i] n % 2 = 0)).card =
      ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card + 2 * r ∧
    ((Finset.range (t + 3 * r)).filter (fun i => collatzStep^[i] n % 2 = 1)).card =
      ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card + r
  | 0 => by simp
  | r + 1 => by
    obtain ⟨ihe, iho⟩ := even_odd_add_three_one ht r
    set m := t + 3 * r
    have hm0 : collatzStep^[m] n = 1 := by
      show collatzStep^[t + 3 * r] n = 1
      rw [Nat.add_comm, Function.iterate_add_apply, ht, iter_three_one r]
    have hm1 : collatzStep^[m + 1] n = 4 := by
      rw [Function.iterate_succ_apply', hm0, collatzStep_one]
    have hm2 : collatzStep^[m + 2] n = 2 := by
      rw [Function.iterate_succ_apply', hm1, collatzStep_four]
    have heq : t + 3 * (r + 1) = ((m + 1) + 1) + 1 := by omega
    rw [heq]
    have hni0e : m ∉ (Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0) := by simp
    have hni0o : m ∉ (Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1) := by simp
    have hni1e : m + 1 ∉ (Finset.range (m + 1)).filter (fun i => collatzStep^[i] n % 2 = 0) := by simp
    have hni1o : m + 1 ∉ (Finset.range (m + 1)).filter (fun i => collatzStep^[i] n % 2 = 1) := by simp
    have hni2e : m + 2 ∉ (Finset.range (m + 2)).filter (fun i => collatzStep^[i] n % 2 = 0) := by simp
    have hni2o : m + 2 ∉ (Finset.range (m + 2)).filter (fun i => collatzStep^[i] n % 2 = 1) := by simp
    constructor
    · rw [Finset.range_add_one, Finset.filter_insert]
      simp only [hm2, Nat.reduceMod, ↓reduceIte, Finset.card_insert_of_notMem hni2e]
      rw [Finset.range_add_one, Finset.filter_insert]
      simp only [hm1, Nat.reduceMod, ↓reduceIte, Finset.card_insert_of_notMem hni1e]
      rw [Finset.range_add_one, Finset.filter_insert]
      simp [hm0, ihe]
      omega
    · rw [Finset.range_add_one, Finset.filter_insert]
      simp only [hm2, Nat.reduceMod, show ¬ (0 = 1) by omega, ↓reduceIte]
      rw [Finset.range_add_one, Finset.filter_insert]
      simp only [hm1, Nat.reduceMod, show ¬ (0 = 1) by omega, ↓reduceIte]
      rw [Finset.range_add_one, Finset.filter_insert]
      simp [hm0, Finset.card_insert_of_notMem hni0o, iho]
      omega

lemma ratio_of_reaches_one {n t : ℕ} (ht : collatzStep^[t] n = 1) :
    ∃ m : ℕ,
      let e := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card
      let o := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card
      3001 ^ o < 2 ^ e * 1000 ^ o := by
  set e0 := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card
  set o0 := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card
  set r := 4 * o0 + 1
  refine ⟨t + 3 * r, ?_⟩
  obtain ⟨he, ho⟩ := even_odd_add_three_one ht r
  dsimp only
  rw [he, ho]
  have hstep : 3001 ^ 5 ≤ 1000 * 4000 ^ 4 := by decide
  have hpow : (3001 ^ 5) ^ o0 ≤ (1000 * 4000 ^ 4) ^ o0 := Nat.pow_le_pow_left hstep o0
  have hlt : 3001 * (3001 ^ 5) ^ o0 < 4000 * (1000 * 4000 ^ 4) ^ o0 := by
    calc 3001 * (3001 ^ 5) ^ o0
        ≤ 3001 * (1000 * 4000 ^ 4) ^ o0 := Nat.mul_le_mul_left 3001 hpow
      _ < 4000 * (1000 * 4000 ^ 4) ^ o0 :=
          Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos (by omega) o0)
  have hlhs : 3001 ^ (o0 + r) = 3001 * (3001 ^ 5) ^ o0 := by
    change 3001 ^ (o0 + (4 * o0 + 1)) = 3001 * (3001 ^ 5) ^ o0
    rw [show o0 + (4 * o0 + 1) = 1 + 5 * o0 by omega, pow_add, pow_one, pow_mul]
  have h4000 : 4000 * (1000 * 4000 ^ 4) ^ o0 = 2 ^ (2 * r) * 1000 ^ (o0 + r) := by
    rw [mul_pow, ← pow_mul]
    have hr1 : 4000 * (1000 ^ o0 * 4000 ^ (4 * o0)) = 1000 ^ o0 * 4000 ^ r := by
      change 4000 * (1000 ^ o0 * 4000 ^ (4 * o0)) = 1000 ^ o0 * 4000 ^ (4 * o0 + 1)
      rw [pow_succ']
      ring
    rw [hr1]
    have h4 : (4000 : ℕ) = 2 ^ 2 * 1000 := by norm_num
    rw [h4, mul_pow, ← pow_mul, pow_add]
    ring
  have hge : 2 ^ (2 * r) * 1000 ^ (o0 + r) ≤ 2 ^ (e0 + 2 * r) * 1000 ^ (o0 + r) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
  calc 3001 ^ (o0 + r)
      = 3001 * (3001 ^ 5) ^ o0 := hlhs
    _ < 4000 * (1000 * 4000 ^ 4) ^ o0 := hlt
    _ = 2 ^ (2 * r) * 1000 ^ (o0 + r) := h4000
    _ ≤ 2 ^ (e0 + 2 * r) * 1000 ^ (o0 + r) := hge

theorem main : H1 → H2 → H3 → OMA.R_CollatzConjecture_collatz_conjecture_R2.H2 := by
  intro h1 h2 h3 n hn h32 hmod3
  by_cases h1024 : n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207,
      223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795,
      799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ)
  · by_cases hlt : n < 10000
    · obtain ⟨t, ht⟩ := h2 n hn hlt h1024 hmod3
      exact ratio_of_reaches_one ht
    · exact h3 n (by omega) h1024 hmod3
  · set r := n % 1024
    have hr_lt : r < 1024 := Nat.mod_lt n (by omega)
    have hr32 : r % 32 = 7 ∨ r % 32 = 15 ∨ r % 32 = 27 ∨ r % 32 = 31 := by
      have hrm : r % 32 = n % 32 := by
        show (n % 1024) % 32 = n % 32
        omega
      omega
    obtain ⟨m0, _, he0, hratio0⟩ := h1 r hr_lt hr32 h1024
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
    have hem_le : ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 0)).card ≤ 10 :=
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
      have hni0 : k ∉ (Finset.range k).filter (fun i => collatzStep^[i] r % 2 = 0) := by simp
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
    have hek_lt : ((Finset.range k).filter (fun i => collatzStep^[i] r % 2 = 0)).card < 10 := by
      have hni0 : k ∉ (Finset.range k).filter (fun i => collatzStep^[i] r % 2 = 0) := by simp
      have he_succ : ((Finset.range m).filter (fun i => collatzStep^[i] r % 2 = 0)).card =
          ((Finset.range k).filter (fun i => collatzStep^[i] r % 2 = 0)).card + 1 := by
        rw [hmk, Finset.range_add_one, Finset.filter_insert]
        simp [hlast_even, Finset.card_insert_of_notMem hni0]
      omega
    have hlt_all : ∀ i < m, ((Finset.range i).filter (fun j => collatzStep^[j] r % 2 = 0)).card < 10 := by
      intro i hi
      exact lt_of_le_of_lt (even_count_mono r (by omega : i ≤ k)) hek_lt
    have hmod_nr : n % 2 ^ 10 = r % 2 ^ 10 := by
      show n % 1024 = (n % 1024) % 1024
      rw [Nat.mod_mod]
    have hpar := (terras_invariance n r m 10 hmod_nr hlt_all).2
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

end OMA.R_CollatzConjecture_collatz_conjecture_R2_H2_R1
