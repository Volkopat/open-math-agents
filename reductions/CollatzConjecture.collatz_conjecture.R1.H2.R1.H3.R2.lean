import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1

-- Reduction CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R2
-- Credit: @Twalways
-- Each H becomes its own step once this file is accepted. Proving all of them closes H3.

/-!
# Sharpened Eliahou-Crandall cycle reduction (mod-128 sieve + cutoff 10000 + period >= 517)

Starting from a putative Collatz cycle minimum `n >= 1000` with `n % 4 = 3` and period `k > 0`,
`main` proves inside Lean:

1. **Mod-128 minimum-of-cycle sieve**: eliminating 19 of the 32 classes with `n % 4 = 3`
   (`3 mod 16`, `11 mod 32`, `23 mod 32`, `7 mod 128`, `15 mod 128`, `59 mod 128`), each via
   an explicit strict descent within at most 11 steps, leaving only 13 surviving classes mod 128.
2. **Exact Crandall-Eliahou cycle corridor**: along one period of length `k = e + o`
   (with `e` even steps and `o` odd steps) staying `>= n`, we have `0 < o`, `3 ^ o < 2 ^ e`,
   and `2 ^ e * n ^ o <= (3 * n + 1) ^ o`.
3. **Three-way split**:
   * `H1` (finite check, 913 integers): every `1000 <= n < 10000` in the 13 surviving mod-128
     classes descends strictly below `n`.
   * `H2` (elementary Diophantine corridor): for all `1 <= o < 200`, `3 ^ o < 2 ^ e` implies
     `30001 ^ o < 2 ^ e * 10000 ^ o`, forcing `o >= 200`, `e >= 317`, and `k >= 517`.
   * `H3` (sharpened open core): no periodic point `n >= 10000` in the 13 surviving mod-128
     classes with `k >= 517`, `o >= 200`, `e >= 317`, `3 ^ o < 2 ^ e`, and
     `2 ^ e * n ^ o <= (3 * n + 1) ^ o` is the minimum of its cycle.
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2

open CollatzConjecture

/-- Finite stopping-time check on the 13 surviving residue classes modulo 128 below 10000
(913 integers total; maximum stopping time is 132). -/
def H1 : Prop :=
  ∀ n : ℕ, 1000 ≤ n → n < 10000 →
    (n % 128 = 27 ∨ n % 128 = 31 ∨ n % 128 = 39 ∨ n % 128 = 47 ∨
     n % 128 = 63 ∨ n % 128 = 71 ∨ n % 128 = 79 ∨ n % 128 = 91 ∨
     n % 128 = 95 ∨ n % 128 = 103 ∨ n % 128 = 111 ∨ n % 128 = 123 ∨ n % 128 = 127) →
    ∃ i : ℕ, collatzStep^[i] n < n

/-- Eliahou-Crandall powers corridor at cutoff 10000: no pair `(o, e)` with `1 <= o < 200`
satisfies both `3 ^ o < 2 ^ e` and `2 ^ e * 10000 ^ o <= 30001 ^ o`. -/
def H2 : Prop :=
  ∀ o e : ℕ, 0 < o → o < 200 → 3 ^ o < 2 ^ e → 30001 ^ o < 2 ^ e * 10000 ^ o

/-- Sharpened open core: no periodic point `n >= 10000` in the 13 surviving mod-128 classes
with period `k >= 517`, odd count `o >= 200`, even count `e >= 317`, and
`3 ^ o < 2 ^ e`, `2 ^ e * n ^ o <= (3 * n + 1) ^ o` is the minimum of its cycle. -/
def H3 : Prop :=
  ∀ n k : ℕ,
    10000 ≤ n →
    (n % 128 = 27 ∨ n % 128 = 31 ∨ n % 128 = 39 ∨ n % 128 = 47 ∨
     n % 128 = 63 ∨ n % 128 = 71 ∨ n % 128 = 79 ∨ n % 128 = 91 ∨
     n % 128 = 95 ∨ n % 128 = 103 ∨ n % 128 = 111 ∨ n % 128 = 123 ∨ n % 128 = 127) →
    517 ≤ k →
    collatzStep^[k] n = n →
    let e := ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 0)).card
    let o := ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card
    200 ≤ o →
    317 ≤ e →
    3 ^ o < 2 ^ e →
    2 ^ e * n ^ o ≤ (3 * n + 1) ^ o →
    ∃ i : ℕ, collatzStep^[i] n < n

lemma collatzStep_even {n : ℕ} (h : n % 2 = 0) : collatzStep n = n / 2 := by
  have he : Even n := Nat.even_iff.mpr h
  simp [collatzStep, he]

lemma collatzStep_odd {n : ℕ} (h : n % 2 = 1) : collatzStep n = 3 * n + 1 := by
  have ho : ¬ Even n := by
    rw [Nat.even_iff]
    omega
  simp [collatzStep, ho]

lemma descent_mod16_3 {n : ℕ} (h : n % 16 = 3) : collatzStep^[6] n < n := by
  have hk : n = 16 * (n / 16) + 3 := by omega
  set k := n / 16
  have h1 : collatzStep (16 * k + 3) = 48 * k + 10 := by rw [collatzStep_odd (by omega)]; omega
  have h2 : collatzStep (48 * k + 10) = 24 * k + 5 := by rw [collatzStep_even (by omega)]; omega
  have h3 : collatzStep (24 * k + 5) = 72 * k + 16 := by rw [collatzStep_odd (by omega)]; omega
  have h4 : collatzStep (72 * k + 16) = 36 * k + 8 := by rw [collatzStep_even (by omega)]; omega
  have h5 : collatzStep (36 * k + 8) = 18 * k + 4 := by rw [collatzStep_even (by omega)]; omega
  have h6 : collatzStep (18 * k + 4) = 9 * k + 2 := by rw [collatzStep_even (by omega)]; omega
  have hval : collatzStep^[6] (16 * k + 3) = 9 * k + 2 := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq, h1, h2, h3, h4, h5, h6]
  rw [hk, hval]
  omega

lemma descent_mod32_11 {n : ℕ} (h : n % 32 = 11) : collatzStep^[8] n < n := by
  have hk : n = 32 * (n / 32) + 11 := by omega
  set k := n / 32
  have h1 : collatzStep (32 * k + 11) = 96 * k + 34 := by rw [collatzStep_odd (by omega)]; omega
  have h2 : collatzStep (96 * k + 34) = 48 * k + 17 := by rw [collatzStep_even (by omega)]; omega
  have h3 : collatzStep (48 * k + 17) = 144 * k + 52 := by rw [collatzStep_odd (by omega)]; omega
  have h4 : collatzStep (144 * k + 52) = 72 * k + 26 := by rw [collatzStep_even (by omega)]; omega
  have h5 : collatzStep (72 * k + 26) = 36 * k + 13 := by rw [collatzStep_even (by omega)]; omega
  have h6 : collatzStep (36 * k + 13) = 108 * k + 40 := by rw [collatzStep_odd (by omega)]; omega
  have h7 : collatzStep (108 * k + 40) = 54 * k + 20 := by rw [collatzStep_even (by omega)]; omega
  have h8 : collatzStep (54 * k + 20) = 27 * k + 10 := by rw [collatzStep_even (by omega)]; omega
  have hval : collatzStep^[8] (32 * k + 11) = 27 * k + 10 := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq,
      h1, h2, h3, h4, h5, h6, h7, h8]
  rw [hk, hval]
  omega

lemma descent_mod32_23 {n : ℕ} (h : n % 32 = 23) : collatzStep^[8] n < n := by
  have hk : n = 32 * (n / 32) + 23 := by omega
  set k := n / 32
  have h1 : collatzStep (32 * k + 23) = 96 * k + 70 := by rw [collatzStep_odd (by omega)]; omega
  have h2 : collatzStep (96 * k + 70) = 48 * k + 35 := by rw [collatzStep_even (by omega)]; omega
  have h3 : collatzStep (48 * k + 35) = 144 * k + 106 := by rw [collatzStep_odd (by omega)]; omega
  have h4 : collatzStep (144 * k + 106) = 72 * k + 53 := by rw [collatzStep_even (by omega)]; omega
  have h5 : collatzStep (72 * k + 53) = 216 * k + 160 := by rw [collatzStep_odd (by omega)]; omega
  have h6 : collatzStep (216 * k + 160) = 108 * k + 80 := by rw [collatzStep_even (by omega)]; omega
  have h7 : collatzStep (108 * k + 80) = 54 * k + 40 := by rw [collatzStep_even (by omega)]; omega
  have h8 : collatzStep (54 * k + 40) = 27 * k + 20 := by rw [collatzStep_even (by omega)]; omega
  have hval : collatzStep^[8] (32 * k + 23) = 27 * k + 20 := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq,
      h1, h2, h3, h4, h5, h6, h7, h8]
  rw [hk, hval]
  omega

lemma descent_mod128_7 {n : ℕ} (h : n % 128 = 7) : collatzStep^[11] n < n := by
  have hk : n = 128 * (n / 128) + 7 := by omega
  set k := n / 128
  have h1 : collatzStep (128 * k + 7) = 384 * k + 22 := by rw [collatzStep_odd (by omega)]; omega
  have h2 : collatzStep (384 * k + 22) = 192 * k + 11 := by rw [collatzStep_even (by omega)]; omega
  have h3 : collatzStep (192 * k + 11) = 576 * k + 34 := by rw [collatzStep_odd (by omega)]; omega
  have h4 : collatzStep (576 * k + 34) = 288 * k + 17 := by rw [collatzStep_even (by omega)]; omega
  have h5 : collatzStep (288 * k + 17) = 864 * k + 52 := by rw [collatzStep_odd (by omega)]; omega
  have h6 : collatzStep (864 * k + 52) = 432 * k + 26 := by rw [collatzStep_even (by omega)]; omega
  have h7 : collatzStep (432 * k + 26) = 216 * k + 13 := by rw [collatzStep_even (by omega)]; omega
  have h8 : collatzStep (216 * k + 13) = 648 * k + 40 := by rw [collatzStep_odd (by omega)]; omega
  have h9 : collatzStep (648 * k + 40) = 324 * k + 20 := by rw [collatzStep_even (by omega)]; omega
  have h10 : collatzStep (324 * k + 20) = 162 * k + 10 := by rw [collatzStep_even (by omega)]; omega
  have h11 : collatzStep (162 * k + 10) = 81 * k + 5 := by rw [collatzStep_even (by omega)]; omega
  have hval : collatzStep^[11] (128 * k + 7) = 81 * k + 5 := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq,
      h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  rw [hk, hval]
  omega

lemma descent_mod128_15 {n : ℕ} (h : n % 128 = 15) : collatzStep^[11] n < n := by
  have hk : n = 128 * (n / 128) + 15 := by omega
  set k := n / 128
  have h1 : collatzStep (128 * k + 15) = 384 * k + 46 := by rw [collatzStep_odd (by omega)]; omega
  have h2 : collatzStep (384 * k + 46) = 192 * k + 23 := by rw [collatzStep_even (by omega)]; omega
  have h3 : collatzStep (192 * k + 23) = 576 * k + 70 := by rw [collatzStep_odd (by omega)]; omega
  have h4 : collatzStep (576 * k + 70) = 288 * k + 35 := by rw [collatzStep_even (by omega)]; omega
  have h5 : collatzStep (288 * k + 35) = 864 * k + 106 := by rw [collatzStep_odd (by omega)]; omega
  have h6 : collatzStep (864 * k + 106) = 432 * k + 53 := by rw [collatzStep_even (by omega)]; omega
  have h7 : collatzStep (432 * k + 53) = 1296 * k + 160 := by rw [collatzStep_odd (by omega)]; omega
  have h8 : collatzStep (1296 * k + 160) = 648 * k + 80 := by rw [collatzStep_even (by omega)]; omega
  have h9 : collatzStep (648 * k + 80) = 324 * k + 40 := by rw [collatzStep_even (by omega)]; omega
  have h10 : collatzStep (324 * k + 40) = 162 * k + 20 := by rw [collatzStep_even (by omega)]; omega
  have h11 : collatzStep (162 * k + 20) = 81 * k + 10 := by rw [collatzStep_even (by omega)]; omega
  have hval : collatzStep^[11] (128 * k + 15) = 81 * k + 10 := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq,
      h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  rw [hk, hval]
  omega

lemma descent_mod128_59 {n : ℕ} (h : n % 128 = 59) : collatzStep^[11] n < n := by
  have hk : n = 128 * (n / 128) + 59 := by omega
  set k := n / 128
  have h1 : collatzStep (128 * k + 59) = 384 * k + 178 := by rw [collatzStep_odd (by omega)]; omega
  have h2 : collatzStep (384 * k + 178) = 192 * k + 89 := by rw [collatzStep_even (by omega)]; omega
  have h3 : collatzStep (192 * k + 89) = 576 * k + 268 := by rw [collatzStep_odd (by omega)]; omega
  have h4 : collatzStep (576 * k + 268) = 288 * k + 134 := by rw [collatzStep_even (by omega)]; omega
  have h5 : collatzStep (288 * k + 134) = 144 * k + 67 := by rw [collatzStep_even (by omega)]; omega
  have h6 : collatzStep (144 * k + 67) = 432 * k + 202 := by rw [collatzStep_odd (by omega)]; omega
  have h7 : collatzStep (432 * k + 202) = 216 * k + 101 := by rw [collatzStep_even (by omega)]; omega
  have h8 : collatzStep (216 * k + 101) = 648 * k + 304 := by rw [collatzStep_odd (by omega)]; omega
  have h9 : collatzStep (648 * k + 304) = 324 * k + 152 := by rw [collatzStep_even (by omega)]; omega
  have h10 : collatzStep (324 * k + 152) = 162 * k + 76 := by rw [collatzStep_even (by omega)]; omega
  have h11 : collatzStep (162 * k + 76) = 81 * k + 38 := by rw [collatzStep_even (by omega)]; omega
  have hval : collatzStep^[11] (128 * k + 59) = 81 * k + 38 := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq,
      h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  rw [hk, hval]
  omega

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

lemma odd_card_pos {n k : ℕ} (hk : 0 < k) (hodd : n % 2 = 1) :
    0 < ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card := by
  apply Finset.card_pos.mpr
  refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by simpa using hodd⟩⟩

lemma lower_prefix_bound (n m : ℕ) :
    3 ^ ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card * n ≤
      2 ^ ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card * collatzStep^[m] n ∧
    (0 < ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card →
      3 ^ ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card * n <
        2 ^ ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card * collatzStep^[m] n) := by
  induction m with
  | zero => simp
  | succ m ih =>
    set e := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card
    set o := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card
    have hm_not : m ∉ Finset.range m := by simp
    have hstep : collatzStep^[m + 1] n = collatzStep (collatzStep^[m] n) :=
      Function.iterate_succ_apply' collatzStep m n
    by_cases hev : collatzStep^[m] n % 2 = 0
    · have hne : ¬ (collatzStep^[m] n % 2 = 1) := by omega
      have he_card :
          ((Finset.range (m + 1)).filter (fun i => collatzStep^[i] n % 2 = 0)).card = e + 1 := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hev, Finset.card_insert_of_notMem]
        simp [hm_not]
      have ho_card :
          ((Finset.range (m + 1)).filter (fun i => collatzStep^[i] n % 2 = 1)).card = o := by
        rw [Finset.range_add_one, Finset.filter_insert, if_neg hne]
      rw [he_card, ho_card, hstep, collatzStep_even hev]
      have hdiv : 2 * (collatzStep^[m] n / 2) = collatzStep^[m] n := by omega
      have hmul : 2 ^ (e + 1) * (collatzStep^[m] n / 2) = 2 ^ e * collatzStep^[m] n := by
        calc
          2 ^ (e + 1) * (collatzStep^[m] n / 2)
              = 2 ^ e * (2 * (collatzStep^[m] n / 2)) := by rw [pow_succ]; ring
          _ = 2 ^ e * collatzStep^[m] n := by rw [hdiv]
      rw [hmul]
      exact ih
    · have hodd : collatzStep^[m] n % 2 = 1 := by omega
      have he_card :
          ((Finset.range (m + 1)).filter (fun i => collatzStep^[i] n % 2 = 0)).card = e := by
        rw [Finset.range_add_one, Finset.filter_insert, if_neg hev]
      have ho_card :
          ((Finset.range (m + 1)).filter (fun i => collatzStep^[i] n % 2 = 1)).card = o + 1 := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hodd, Finset.card_insert_of_notMem]
        simp [hm_not]
      rw [he_card, ho_card, hstep, collatzStep_odd hodd]
      have h2pos : 0 < 2 ^ e := Nat.pow_pos (by decide)
      have hlt : 3 ^ (o + 1) * n < 2 ^ e * (3 * collatzStep^[m] n + 1) := by
        have hle := ih.1
        calc
          3 ^ (o + 1) * n = 3 * (3 ^ o * n) := by rw [pow_succ]; ring
          _ ≤ 3 * (2 ^ e * collatzStep^[m] n) := Nat.mul_le_mul_left 3 hle
          _ < 3 * (2 ^ e * collatzStep^[m] n) + 2 ^ e := by omega
          _ = 2 ^ e * (3 * collatzStep^[m] n + 1) := by ring
      exact ⟨hlt.le, fun _ => hlt⟩

lemma upper_prefix_bound (n m : ℕ) (hge : ∀ t ≤ m, n ≤ collatzStep^[t] n) :
    2 ^ ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card *
      n ^ ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card *
      collatzStep^[m] n ≤
    (3 * n + 1) ^ ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card * n := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ih' := ih (fun t ht => hge t (Nat.le_succ_of_le ht))
    set e := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card
    set o := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card
    have hm_not : m ∉ Finset.range m := by simp
    have hstep : collatzStep^[m + 1] n = collatzStep (collatzStep^[m] n) :=
      Function.iterate_succ_apply' collatzStep m n
    by_cases hev : collatzStep^[m] n % 2 = 0
    · have hne : ¬ (collatzStep^[m] n % 2 = 1) := by omega
      have he_card :
          ((Finset.range (m + 1)).filter (fun i => collatzStep^[i] n % 2 = 0)).card = e + 1 := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hev, Finset.card_insert_of_notMem]
        simp [hm_not]
      have ho_card :
          ((Finset.range (m + 1)).filter (fun i => collatzStep^[i] n % 2 = 1)).card = o := by
        rw [Finset.range_add_one, Finset.filter_insert, if_neg hne]
      rw [he_card, ho_card, hstep, collatzStep_even hev]
      have hdiv : 2 * (collatzStep^[m] n / 2) = collatzStep^[m] n := by omega
      calc
        2 ^ (e + 1) * n ^ o * (collatzStep^[m] n / 2)
            = 2 ^ e * n ^ o * (2 * (collatzStep^[m] n / 2)) := by rw [pow_succ]; ring
        _ = 2 ^ e * n ^ o * collatzStep^[m] n := by rw [hdiv]
        _ ≤ (3 * n + 1) ^ o * n := ih'
    · have hodd : collatzStep^[m] n % 2 = 1 := by omega
      have he_card :
          ((Finset.range (m + 1)).filter (fun i => collatzStep^[i] n % 2 = 0)).card = e := by
        rw [Finset.range_add_one, Finset.filter_insert, if_neg hev]
      have ho_card :
          ((Finset.range (m + 1)).filter (fun i => collatzStep^[i] n % 2 = 1)).card = o + 1 := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hodd, Finset.card_insert_of_notMem]
        simp [hm_not]
      rw [he_card, ho_card, hstep, collatzStep_odd hodd]
      have hge_m : n ≤ collatzStep^[m] n := hge m (Nat.le_succ m)
      have hmul_step : n * (3 * collatzStep^[m] n + 1) ≤ (3 * n + 1) * collatzStep^[m] n := by
        nlinarith
      calc
        2 ^ e * n ^ (o + 1) * (3 * collatzStep^[m] n + 1)
            = 2 ^ e * n ^ o * (n * (3 * collatzStep^[m] n + 1)) := by rw [pow_succ]; ring
        _ ≤ 2 ^ e * n ^ o * ((3 * n + 1) * collatzStep^[m] n) := Nat.mul_le_mul_left _ hmul_step
        _ = (3 * n + 1) * (2 ^ e * n ^ o * collatzStep^[m] n) := by ring
        _ ≤ (3 * n + 1) * ((3 * n + 1) ^ o * n) := Nat.mul_le_mul_left _ ih'
        _ = (3 * n + 1) ^ (o + 1) * n := by rw [pow_succ]; ring

lemma pow_two_316_lt_pow_three_200 : (2 : ℕ) ^ 316 < 3 ^ 200 := by
  have h : (2 : ℕ) ^ 79 < 3 ^ 50 := by norm_num
  have h4 : ((2 : ℕ) ^ 79) ^ 4 < (3 ^ 50) ^ 4 := Nat.pow_lt_pow_left h (by decide)
  rw [← pow_mul, ← pow_mul] at h4
  exact h4

theorem main : H1 → H2 → H3 → OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1.H3 := by
  intro h1 h2 h3 n k hn1000 hmod4 hk hcyc
  by_cases h16 : n % 16 = 3
  · exact ⟨6, descent_mod16_3 h16⟩
  · by_cases h32a : n % 32 = 11
    · exact ⟨8, descent_mod32_11 h32a⟩
    · by_cases h32b : n % 32 = 23
      · exact ⟨8, descent_mod32_23 h32b⟩
      · by_cases h128a : n % 128 = 7
        · exact ⟨11, descent_mod128_7 h128a⟩
        · by_cases h128b : n % 128 = 15
          · exact ⟨11, descent_mod128_15 h128b⟩
          · by_cases h128c : n % 128 = 59
            · exact ⟨11, descent_mod128_59 h128c⟩
            · have hsurv :
                  n % 128 = 27 ∨ n % 128 = 31 ∨ n % 128 = 39 ∨ n % 128 = 47 ∨
                  n % 128 = 63 ∨ n % 128 = 71 ∨ n % 128 = 79 ∨ n % 128 = 91 ∨
                  n % 128 = 95 ∨ n % 128 = 103 ∨ n % 128 = 111 ∨ n % 128 = 123 ∨
                  n % 128 = 127 := by omega
              by_cases hsmall : n < 10000
              · exact h1 n hn1000 hsmall hsurv
              · have hge10000 : 10000 ≤ n := by omega
                by_contra! hmin
                set e := ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 0)).card
                set o := ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card
                have heo : e + o = k := even_add_odd_card n k
                have ho_pos : 0 < o := odd_card_pos hk (by omega)
                have hlow_mul := (lower_prefix_bound n k).2 ho_pos
                rw [hcyc] at hlow_mul
                have hlow : 3 ^ o < 2 ^ e := Nat.lt_of_mul_lt_mul_right hlow_mul
                have hup_mul := upper_prefix_bound n k (fun t _ => hmin t)
                rw [hcyc] at hup_mul
                have hup : 2 ^ e * n ^ o ≤ (3 * n + 1) ^ o :=
                  Nat.le_of_mul_le_mul_right hup_mul (by omega : 0 < n)
                have hlin : 10000 * (3 * n + 1) ≤ 30001 * n := by omega
                have hpow : (10000 * (3 * n + 1)) ^ o ≤ (30001 * n) ^ o :=
                  Nat.pow_le_pow_left hlin o
                have hup10000_mul : 2 ^ e * 10000 ^ o * n ^ o ≤ 30001 ^ o * n ^ o := calc
                  2 ^ e * 10000 ^ o * n ^ o
                      = 10000 ^ o * (2 ^ e * n ^ o) := by ring
                  _ ≤ 10000 ^ o * (3 * n + 1) ^ o := Nat.mul_le_mul_left _ hup
                  _ = (10000 * (3 * n + 1)) ^ o := by rw [mul_pow]
                  _ ≤ (30001 * n) ^ o := hpow
                  _ = 30001 ^ o * n ^ o := by rw [mul_pow]
                have hup10000 : 2 ^ e * 10000 ^ o ≤ 30001 ^ o :=
                  Nat.le_of_mul_le_mul_right hup10000_mul (Nat.pow_pos (by omega))
                have ho200 : 200 ≤ o := by
                  by_contra! holt
                  have hbad := h2 o e ho_pos holt hlow
                  omega
                have he317 : 317 ≤ e := by
                  have h3le : (3 : ℕ) ^ 200 ≤ 3 ^ o := Nat.pow_le_pow_right (by decide) ho200
                  have h2lt : (2 : ℕ) ^ 316 < 2 ^ e :=
                    lt_trans pow_two_316_lt_pow_three_200 (lt_of_le_of_lt h3le hlow)
                  have hlt316 : 316 < e :=
                    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2lt
                  omega
                have hk517 : 517 ≤ k := by omega
                obtain ⟨i, hi⟩ := h3 n k hge10000 hsurv hk517 hcyc ho200 he317 hlow hup
                exact not_lt_of_ge (hmin i) hi

end OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2
