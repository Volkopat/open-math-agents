import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H1_R1

-- Reduction CollatzConjecture.collatz_conjecture.R1.H1.R1.H1.R1 of step CollatzConjecture.collatz_conjecture.R1.H1.R1.H1
-- Credit: @Twalways

/-!
# Terras modular invariance, mod-1024 sieve, and global linear odd-density corridor

For a putative never-descending divergent orbit starting at `n >= 10000` that never contracts
(`∀ t, 2 ^ e(n, t) <= 3 ^ o(n, t)`), `main` proves inside Lean:

1. **Terras's Modular Invariance Theorem (1976, Theorem 1.1)** for every `k : ℕ`:
   if the residue `r = n % 2 ^ k` contracts (`3 ^ o < 2 ^ e`) within `e <= k` halvings, then `n`
   itself contracts (by minimality of the first contracting step, its last step is even, so all
   earlier steps satisfy `e < k` and hence `collatzStep^[i] n ≡ collatzStep^[i] r (mod 2 ^ (k - e))`).
2. **Global linear odd-density corridor**: since `3 ^ 5 = 243 < 256 = 2 ^ 8` and no two
   consecutive ordinary steps are odd, any non-contracting orbit satisfies for every `t > 0`:
   `5 * t < 13 * o(n, t)`, `13 * e(n, t) < 8 * t`, and `o(n, t) <= e(n, t) + 1`.

This splits `R1.H1.R1.H1` into:
* `H1` (finite mod-1024 Terras sieve, directly provable in Lean): among the 104 mod-1024 lifts
  of the 13 mod-128 classes, the 40 classes outside the 64 surviving mod-1024 classes all
  contract within `e <= 10` halvings (eliminating 93.75% of all integers).
* `H2` (sharpened open core): no never-descending divergent `n >= 10000` in the 64 surviving
  mod-1024 classes simultaneously stays inside every Terras cylinder (`∀ k t, e(n % 2^k, t) <= k
  -> 2^e <= 3^o`) and the global linear odd-density corridor (`5*t < 13*o`, `13*e < 8*t`,
  `o <= e + 1` for all `t > 0`).
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1

open CollatzConjecture OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1

/-- Finite mod-1024 Terras sieve: every residue `r < 1024` in the 13 mod-128 classes outside the
64 surviving mod-1024 classes contracts (`3 ^ o < 2 ^ e`) within `e <= 10` halvings. -/
def H1 : Prop :=
  ∀ r : ℕ, r < 1024 →
    (r % 128 = 27 ∨ r % 128 = 31 ∨ r % 128 = 39 ∨ r % 128 = 47 ∨
     r % 128 = 63 ∨ r % 128 = 71 ∨ r % 128 = 79 ∨ r % 128 = 91 ∨
     r % 128 = 95 ∨ r % 128 = 103 ∨ r % 128 = 111 ∨ r % 128 = 123 ∨ r % 128 = 127) →
    r ∉ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
          239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
          511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
          767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    ∃ t : ℕ,
      ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 0)).card ≤ 10 ∧
      3 ^ ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 1)).card <
      2 ^ ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 0)).card

/-- Sharpened open core: no never-descending divergent seed `n >= 10000` in the 64 surviving
mod-1024 classes lies in every Terras non-contracting cylinder mod `2 ^ k` while satisfying
`5 * t < 13 * o`, `13 * e < 8 * t`, and `o <= e + 1` for all `t > 0`. -/
def H2 : Prop :=
  ∀ n : ℕ, 10000 ≤ n →
    n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
                 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
                 511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
                 767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    (∀ t : ℕ, n ≤ collatzStep^[t] n) →
    (∀ B : ℕ, ∃ t : ℕ, B < collatzStep^[t] n) →
    (∀ k t : ℕ,
      ((Finset.range t).filter (fun i => collatzStep^[i] (n % 2 ^ k) % 2 = 0)).card ≤ k →
      2 ^ ((Finset.range t).filter (fun i => collatzStep^[i] (n % 2 ^ k) % 2 = 0)).card ≤
      3 ^ ((Finset.range t).filter (fun i => collatzStep^[i] (n % 2 ^ k) % 2 = 1)).card) →
    (∀ t : ℕ, 0 < t →
      let e := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card
      let o := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card
      5 * t < 13 * o ∧ 13 * e < 8 * t ∧ o ≤ e + 1) →
    False

lemma parity_of_mod_pow_pos {a b d : ℕ} (hd : 1 ≤ d) (h : a % 2 ^ d = b % 2 ^ d) :
    a % 2 = b % 2 := by
  have hdvd : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
  rw [← Nat.mod_mod_of_dvd a hdvd, h, Nat.mod_mod_of_dvd b hdvd]

lemma mod_div_two {a b d : ℕ} (h : a % 2 ^ (d + 1) = b % 2 ^ (d + 1))
    (ha : a % 2 = 0) (hb : b % 2 = 0) : (a / 2) % 2 ^ d = (b / 2) % 2 ^ d := by
  have ha' : a = 2 * (a / 2) := by omega
  have hb' : b = 2 * (b / 2) := by omega
  have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ']
  rw [ha', hb', hp, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h
  omega

lemma mod_three_mul_add_one {a b m : ℕ} (h : a % m = b % m) :
    (3 * a + 1) % m = (3 * b + 1) % m := by
  simp [Nat.add_mod, Nat.mul_mod, h]

lemma even_card_mono {x a b : ℕ} (hab : a ≤ b) :
    ((Finset.range a).filter (fun j => collatzStep^[j] x % 2 = 0)).card ≤
    ((Finset.range b).filter (fun j => collatzStep^[j] x % 2 = 0)).card := by
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨lt_of_lt_of_le hj.1 hab, hj.2⟩

lemma terras_invariance_aux (n r k m : ℕ) (hmod : n % 2 ^ k = r % 2 ^ k)
    (he : ∀ i < m, ((Finset.range i).filter (fun j => collatzStep^[j] r % 2 = 0)).card < k) :
    collatzStep^[m] n % 2 ^ (k - ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 0)).card) =
      collatzStep^[m] r % 2 ^ (k - ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 0)).card) ∧
    ((Finset.range m).filter (fun j => collatzStep^[j] n % 2 = 0)).card =
      ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 0)).card ∧
    ((Finset.range m).filter (fun j => collatzStep^[j] n % 2 = 1)).card =
      ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 1)).card := by
  induction m with
  | zero => simpa using hmod
  | succ m ih =>
    obtain ⟨hcong, heq_e, heq_o⟩ := ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
    have hlt_k : ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 0)).card < k :=
      he m (Nat.lt_succ_self m)
    have hpar : collatzStep^[m] n % 2 = collatzStep^[m] r % 2 :=
      parity_of_mod_pow_pos (by omega) hcong
    have hm_not : m ∉ Finset.range m := by simp
    have hstep_n : collatzStep^[m + 1] n = collatzStep (collatzStep^[m] n) :=
      Function.iterate_succ_apply' collatzStep m n
    have hstep_r : collatzStep^[m + 1] r = collatzStep (collatzStep^[m] r) :=
      Function.iterate_succ_apply' collatzStep m r
    by_cases hev_r : collatzStep^[m] r % 2 = 0
    · have hev_n : collatzStep^[m] n % 2 = 0 := by omega
      have hne_r : ¬ (collatzStep^[m] r % 2 = 1) := by omega
      have hne_n : ¬ (collatzStep^[m] n % 2 = 1) := by omega
      have her' : ((Finset.range (m + 1)).filter (fun j => collatzStep^[j] r % 2 = 0)).card =
          ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 0)).card + 1 := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hev_r, Finset.card_insert_of_notMem]
        simp [hm_not]
      have hen' : ((Finset.range (m + 1)).filter (fun j => collatzStep^[j] n % 2 = 0)).card =
          ((Finset.range m).filter (fun j => collatzStep^[j] n % 2 = 0)).card + 1 := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hev_n, Finset.card_insert_of_notMem]
        simp [hm_not]
      have hor' : ((Finset.range (m + 1)).filter (fun j => collatzStep^[j] r % 2 = 1)).card =
          ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 1)).card := by
        rw [Finset.range_add_one, Finset.filter_insert, if_neg hne_r]
      have hon' : ((Finset.range (m + 1)).filter (fun j => collatzStep^[j] n % 2 = 1)).card =
          ((Finset.range m).filter (fun j => collatzStep^[j] n % 2 = 1)).card := by
        rw [Finset.range_add_one, Finset.filter_insert, if_neg hne_n]
      rw [her', hen', hor', hon', hstep_n, hstep_r, collatzStep_even hev_n, collatzStep_even hev_r]
      refine ⟨?_, by omega, heq_o⟩
      set d := k - (((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 0)).card + 1)
      have hd : k - ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 0)).card = d + 1 := by
        dsimp [d]; omega
      rw [hd] at hcong
      exact mod_div_two hcong hev_n hev_r
    · have hodd_r : collatzStep^[m] r % 2 = 1 := by omega
      have hodd_n : collatzStep^[m] n % 2 = 1 := by omega
      have hne_n : ¬ (collatzStep^[m] n % 2 = 0) := by omega
      have her' : ((Finset.range (m + 1)).filter (fun j => collatzStep^[j] r % 2 = 0)).card =
          ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 0)).card := by
        rw [Finset.range_add_one, Finset.filter_insert, if_neg hev_r]
      have hen' : ((Finset.range (m + 1)).filter (fun j => collatzStep^[j] n % 2 = 0)).card =
          ((Finset.range m).filter (fun j => collatzStep^[j] n % 2 = 0)).card := by
        rw [Finset.range_add_one, Finset.filter_insert, if_neg hne_n]
      have hor' : ((Finset.range (m + 1)).filter (fun j => collatzStep^[j] r % 2 = 1)).card =
          ((Finset.range m).filter (fun j => collatzStep^[j] r % 2 = 1)).card + 1 := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hodd_r, Finset.card_insert_of_notMem]
        simp [hm_not]
      have hon' : ((Finset.range (m + 1)).filter (fun j => collatzStep^[j] n % 2 = 1)).card =
          ((Finset.range m).filter (fun j => collatzStep^[j] n % 2 = 1)).card + 1 := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hodd_n, Finset.card_insert_of_notMem]
        simp [hm_not]
      rw [her', hen', hor', hon', hstep_n, hstep_r, collatzStep_odd hodd_n, collatzStep_odd hodd_r]
      exact ⟨mod_three_mul_add_one hcong, heq_e, by omega⟩

lemma terras_lift (n k t : ℕ)
    (he : ((Finset.range t).filter (fun i => collatzStep^[i] (n % 2 ^ k) % 2 = 0)).card ≤ k)
    (h3 : 3 ^ ((Finset.range t).filter (fun i => collatzStep^[i] (n % 2 ^ k) % 2 = 1)).card <
          2 ^ ((Finset.range t).filter (fun i => collatzStep^[i] (n % 2 ^ k) % 2 = 0)).card) :
    ∃ t' : ℕ,
      3 ^ ((Finset.range t').filter (fun i => collatzStep^[i] n % 2 = 1)).card <
      2 ^ ((Finset.range t').filter (fun i => collatzStep^[i] n % 2 = 0)).card := by
  classical
  set r := n % 2 ^ k
  have hex : ∃ s : ℕ,
      3 ^ ((Finset.range s).filter (fun i => collatzStep^[i] r % 2 = 1)).card <
      2 ^ ((Finset.range s).filter (fun i => collatzStep^[i] r % 2 = 0)).card := ⟨t, h3⟩
  set t' := Nat.find hex
  have ht'_spec :
      3 ^ ((Finset.range t').filter (fun i => collatzStep^[i] r % 2 = 1)).card <
      2 ^ ((Finset.range t').filter (fun i => collatzStep^[i] r % 2 = 0)).card := Nat.find_spec hex
  have ht'_le : t' ≤ t := Nat.find_min' hex h3
  have ht'_pos : 0 < t' := by
    by_contra! hz
    have h0 : t' = 0 := by omega
    rw [h0] at ht'_spec
    simp at ht'_spec
  have he_t' : ((Finset.range t').filter (fun i => collatzStep^[i] r % 2 = 0)).card ≤ k :=
    le_trans (even_card_mono ht'_le) he
  set p := t' - 1
  have hp_succ : p + 1 = t' := by omega
  have hp_not : ¬ (3 ^ ((Finset.range p).filter (fun i => collatzStep^[i] r % 2 = 1)).card <
      2 ^ ((Finset.range p).filter (fun i => collatzStep^[i] r % 2 = 0)).card) :=
    Nat.find_min hex (show p < t' by omega)
  have hp_even : collatzStep^[p] r % 2 = 0 := by
    by_contra hne
    have hodd : collatzStep^[p] r % 2 = 1 := by omega
    have hp_mem : p ∉ Finset.range p := by simp
    have he_eq : ((Finset.range t').filter (fun i => collatzStep^[i] r % 2 = 0)).card =
        ((Finset.range p).filter (fun i => collatzStep^[i] r % 2 = 0)).card := by
      rw [← hp_succ, Finset.range_add_one, Finset.filter_insert, if_neg hne]
    have ho_eq : ((Finset.range t').filter (fun i => collatzStep^[i] r % 2 = 1)).card =
        ((Finset.range p).filter (fun i => collatzStep^[i] r % 2 = 1)).card + 1 := by
      rw [← hp_succ, Finset.range_add_one, Finset.filter_insert, if_pos hodd, Finset.card_insert_of_notMem]
      simp [hp_mem]
    rw [he_eq, ho_eq, pow_succ] at ht'_spec
    have h3pos : 0 < 3 ^ ((Finset.range p).filter (fun i => collatzStep^[i] r % 2 = 1)).card :=
      Nat.pow_pos (by decide)
    omega
  have he_p : ((Finset.range p).filter (fun i => collatzStep^[i] r % 2 = 0)).card < k := by
    have hp_mem : p ∉ Finset.range p := by simp
    have he_succ : ((Finset.range t').filter (fun i => collatzStep^[i] r % 2 = 0)).card =
        ((Finset.range p).filter (fun i => collatzStep^[i] r % 2 = 0)).card + 1 := by
      rw [← hp_succ, Finset.range_add_one, Finset.filter_insert, if_pos hp_even, Finset.card_insert_of_notMem]
      simp [hp_mem]
    omega
  have he_all : ∀ i < t', ((Finset.range i).filter (fun j => collatzStep^[j] r % 2 = 0)).card < k := by
    intro i hi
    exact lt_of_le_of_lt (even_card_mono (show i ≤ p by omega)) he_p
  have hmod : n % 2 ^ k = r % 2 ^ k := by
    dsimp [r]
    rw [Nat.mod_mod]
  obtain ⟨_, he_eq, ho_eq⟩ := terras_invariance_aux n r k t' hmod he_all
  exact ⟨t', by rw [he_eq, ho_eq]; exact ht'_spec⟩

lemma even_add_odd_card (n m : ℕ) :
    ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card +
    ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm_not : m ∉ Finset.range m := by simp
    by_cases hev : collatzStep^[m] n % 2 = 0
    · have hne : ¬ (collatzStep^[m] n % 2 = 1) := by omega
      rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
        if_pos hev, if_neg hne, Finset.card_insert_of_notMem (by simp [hm_not])]
      omega
    · have hodd : collatzStep^[m] n % 2 = 1 := by omega
      rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
        if_neg hev, if_pos hodd, Finset.card_insert_of_notMem (by simp [hm_not])]
      omega

lemma odd_le_even_add_one (n m : ℕ) :
    ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card ≤
      ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card + 1 ∧
    (collatzStep^[m] n % 2 = 1 →
      ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card ≤
      ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm_not : m ∉ Finset.range m := by simp
    have hstep : collatzStep^[m + 1] n = collatzStep (collatzStep^[m] n) :=
      Function.iterate_succ_apply' collatzStep m n
    by_cases hev : collatzStep^[m] n % 2 = 0
    · have hne : ¬ (collatzStep^[m] n % 2 = 1) := by omega
      rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
        if_pos hev, if_neg hne, Finset.card_insert_of_notMem (by simp [hm_not])]
      exact ⟨by omega, fun _ => ih.1⟩
    · have hodd : collatzStep^[m] n % 2 = 1 := by omega
      rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
        if_neg hev, if_pos hodd, Finset.card_insert_of_notMem (by simp [hm_not])]
      have hnext_even : collatzStep^[m + 1] n % 2 = 0 := by
        rw [hstep, collatzStep_odd hodd]
        omega
      have hle := ih.2 hodd
      exact ⟨by omega, fun h => by omega⟩

lemma linear_density_of_noncontract {n t : ℕ} (hodd : n % 2 = 1) (ht : 0 < t)
    (hnc : 2 ^ ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card ≤
           3 ^ ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card) :
    5 * t < 13 * ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card ∧
    13 * ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card < 8 * t := by
  set e := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card
  set o := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card
  have heo : e + o = t := even_add_odd_card n t
  have ho_pos : 0 < o := by
    apply Finset.card_pos.mpr
    exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, by simpa using hodd⟩⟩
  have h5 : (2 ^ e) ^ 5 ≤ (3 ^ o) ^ 5 := Nat.pow_le_pow_left hnc 5
  have h25 : (2 : ℕ) ^ (5 * e) ≤ (3 ^ 5) ^ o := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm e 5, Nat.mul_comm o 5, pow_mul 3 5 o] at h5
    exact h5
  have h35 : (3 : ℕ) ^ 5 < 2 ^ 8 := by decide
  have hpow_lt : (3 ^ 5) ^ o < (2 ^ 8) ^ o := Nat.pow_lt_pow_left h35 (by omega)
  have h2lt : (2 : ℕ) ^ (5 * e) < 2 ^ (8 * o) := by
    have h8o : (2 ^ 8) ^ o = 2 ^ (8 * o) := by rw [← pow_mul]
    rw [h8o] at hpow_lt
    exact lt_of_le_of_lt h25 hpow_lt
  have hlin : 5 * e < 8 * o := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2lt
  omega

theorem main : H1 → H2 → OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1.H1 := by
  intro h1 h2 n hn10000 h128 hmin hunb
  by_contra! hnc
  have hcyl : ∀ k t : ℕ,
      ((Finset.range t).filter (fun i => collatzStep^[i] (n % 2 ^ k) % 2 = 0)).card ≤ k →
      2 ^ ((Finset.range t).filter (fun i => collatzStep^[i] (n % 2 ^ k) % 2 = 0)).card ≤
      3 ^ ((Finset.range t).filter (fun i => collatzStep^[i] (n % 2 ^ k) % 2 = 1)).card := by
    intro k t he
    by_contra! hlt
    obtain ⟨t', ht'⟩ := terras_lift n k t he hlt
    exact not_lt_of_ge (hnc t') ht'
  have h1024 : n % 1024 ∈ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
      239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
      511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
      767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) := by
    by_contra hnot
    have hr128 : (n % 1024) % 128 = n % 128 := Nat.mod_mod_of_dvd n (by decide : 128 ∣ 1024)
    have h128' : (n % 1024) % 128 = 27 ∨ (n % 1024) % 128 = 31 ∨ (n % 1024) % 128 = 39 ∨
        (n % 1024) % 128 = 47 ∨ (n % 1024) % 128 = 63 ∨ (n % 1024) % 128 = 71 ∨
        (n % 1024) % 128 = 79 ∨ (n % 1024) % 128 = 91 ∨ (n % 1024) % 128 = 95 ∨
        (n % 1024) % 128 = 103 ∨ (n % 1024) % 128 = 111 ∨ (n % 1024) % 128 = 123 ∨
        (n % 1024) % 128 = 127 := by rw [hr128]; exact h128
    obtain ⟨t, hte, ht3⟩ := h1 (n % 1024) (Nat.mod_lt n (by decide)) h128' hnot
    have h10 : (2 : ℕ) ^ 10 = 1024 := by decide
    rw [← h10] at hte ht3
    exact not_lt_of_ge (hcyl 10 t hte) ht3
  have hodd_n : n % 2 = 1 := by omega
  have hlin : ∀ t : ℕ, 0 < t →
      let e := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card
      let o := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card
      5 * t < 13 * o ∧ 13 * e < 8 * t ∧ o ≤ e + 1 := by
    intro t ht
    obtain ⟨ha, hb⟩ := linear_density_of_noncontract hodd_n ht (hnc t)
    exact ⟨ha, hb, (odd_le_even_add_one n t).1⟩
  exact h2 n hn10000 h1024 hmin hunb hcyl hlin

end OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1
