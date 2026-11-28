import FormalConjectures.Wikipedia.CollatzConjecture

-- Reduction CollatzConjecture.collatz_conjecture.R2 of Collatz conjecture
-- Credit: @Twalways
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Collatz = finite base check + symbolic halving-ratio contraction on hard mod-96 classes

This reduction is independent of `R1` (boundedness + no nontrivial cycles). Instead of tracking
trajectory heights or excluding cycles separately, it reduces the Collatz conjecture to:

* `H1` (finite base check): every `0 < n < 1000` reaches `1`.
* `H2` (symbolic halving-ratio contraction): for every `n ≥ 1000` surviving the combined
  mod-32 forward stopping-time sieve (`n % 32 ∈ {7, 15, 27, 31}`) and mod-3 backward 2-step
  coalescence sieve (`n % 3 ≠ 2`) — only 8 of 96 residue classes — the trajectory eventually
  reaches a prefix whose even-step count `e` and odd-step count `o` satisfy
  `3001 ^ o < 2 ^ e * 1000 ^ o` (i.e. `e / o > log₂(3.001) ≈ 1.58544`).

`main` proves inside Lean that:
1. 88 of 96 residue classes either descend strictly below `n` within at most 8 steps
   (`0 mod 2`, `1 mod 4`, `3 mod 16`, `11 mod 32`, `23 mod 32`) or coalesce in 2 steps with
   the smaller odd integer `(2n - 1) / 3` (`5 mod 6`).
2. Along any non-descending prefix of length `m` from `n ≥ 1000`, the exact multiplicative
   bound `2 ^ e * n ^ o * C^[m] n ≤ (3 * n + 1) ^ o * n` holds, so `3001 ^ o < 2 ^ e * 1000 ^ o`
   forces a strict descent `C^[t] n < n` for some `t ≤ m`.
3. Strong induction then closes the conjecture from `H1` and `H2`.
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R2

open CollatzConjecture

/-- Finite base verification: every positive integer below 1000 reaches 1. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → n < 1000 → ∃ m : ℕ, collatzStep^[m] n = 1

/-- Symbolic halving-ratio contraction on the 8 surviving residue classes modulo 96:
for every `n ≥ 1000` with `n % 32 ∈ {7, 15, 27, 31}` and `n % 3 ≠ 2`, there exists `m`
such that the even-step count `e` and odd-step count `o` in the first `m` steps satisfy
`3001 ^ o < 2 ^ e * 1000 ^ o`. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000 ≤ n →
    (n % 32 = 7 ∨ n % 32 = 15 ∨ n % 32 = 27 ∨ n % 32 = 31) →
    n % 3 ≠ 2 →
    ∃ m : ℕ,
      let e := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card
      let o := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card
      3001 ^ o < 2 ^ e * 1000 ^ o

lemma collatzStep_even {n : ℕ} (h : n % 2 = 0) : collatzStep n = n / 2 := by
  have he : Even n := Nat.even_iff.mpr h
  simp [collatzStep, he]

lemma collatzStep_odd {n : ℕ} (h : n % 2 = 1) : collatzStep n = 3 * n + 1 := by
  have ho : ¬ Even n := by
    rw [Nat.even_iff]
    omega
  simp [collatzStep, ho]

lemma step_pos {n : ℕ} (hn : 0 < n) : 0 < collatzStep n := by
  by_cases h : n % 2 = 0
  · rw [collatzStep_even h]; omega
  · rw [collatzStep_odd (by omega)]; omega

lemma iterate_pos {n : ℕ} (hn : 0 < n) (m : ℕ) : 0 < collatzStep^[m] n := by
  induction m generalizing n with
  | zero => simpa using hn
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih (step_pos hn)

lemma descent_even {n : ℕ} (hn : 1 < n) (h : n % 2 = 0) :
    collatzStep^[1] n < n := by
  simp only [Function.iterate_one, collatzStep_even h]
  omega

lemma descent_mod4_1 {n : ℕ} (hn : 1 < n) (h : n % 4 = 1) :
    collatzStep^[3] n < n := by
  have hk : n = 4 * (n / 4) + 1 := by omega
  set k := n / 4
  have h1 : collatzStep (4 * k + 1) = 12 * k + 4 := by
    rw [collatzStep_odd (by omega)]; omega
  have h2 : collatzStep (12 * k + 4) = 6 * k + 2 := by
    rw [collatzStep_even (by omega)]; omega
  have h3 : collatzStep (6 * k + 2) = 3 * k + 1 := by
    rw [collatzStep_even (by omega)]; omega
  have hval : collatzStep^[3] (4 * k + 1) = 3 * k + 1 := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq, h1, h2, h3]
  rw [hk, hval]
  omega

lemma descent_mod16_3 {n : ℕ} (h : n % 16 = 3) :
    collatzStep^[6] n < n := by
  have hk : n = 16 * (n / 16) + 3 := by omega
  set k := n / 16
  have h1 : collatzStep (16 * k + 3) = 48 * k + 10 := by
    rw [collatzStep_odd (by omega)]; omega
  have h2 : collatzStep (48 * k + 10) = 24 * k + 5 := by
    rw [collatzStep_even (by omega)]; omega
  have h3 : collatzStep (24 * k + 5) = 72 * k + 16 := by
    rw [collatzStep_odd (by omega)]; omega
  have h4 : collatzStep (72 * k + 16) = 36 * k + 8 := by
    rw [collatzStep_even (by omega)]; omega
  have h5 : collatzStep (36 * k + 8) = 18 * k + 4 := by
    rw [collatzStep_even (by omega)]; omega
  have h6 : collatzStep (18 * k + 4) = 9 * k + 2 := by
    rw [collatzStep_even (by omega)]; omega
  have hval : collatzStep^[6] (16 * k + 3) = 9 * k + 2 := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq, h1, h2, h3, h4, h5, h6]
  rw [hk, hval]
  omega

lemma descent_mod32_11 {n : ℕ} (h : n % 32 = 11) :
    collatzStep^[8] n < n := by
  have hk : n = 32 * (n / 32) + 11 := by omega
  set k := n / 32
  have h1 : collatzStep (32 * k + 11) = 96 * k + 34 := by
    rw [collatzStep_odd (by omega)]; omega
  have h2 : collatzStep (96 * k + 34) = 48 * k + 17 := by
    rw [collatzStep_even (by omega)]; omega
  have h3 : collatzStep (48 * k + 17) = 144 * k + 52 := by
    rw [collatzStep_odd (by omega)]; omega
  have h4 : collatzStep (144 * k + 52) = 72 * k + 26 := by
    rw [collatzStep_even (by omega)]; omega
  have h5 : collatzStep (72 * k + 26) = 36 * k + 13 := by
    rw [collatzStep_even (by omega)]; omega
  have h6 : collatzStep (36 * k + 13) = 108 * k + 40 := by
    rw [collatzStep_odd (by omega)]; omega
  have h7 : collatzStep (108 * k + 40) = 54 * k + 20 := by
    rw [collatzStep_even (by omega)]; omega
  have h8 : collatzStep (54 * k + 20) = 27 * k + 10 := by
    rw [collatzStep_even (by omega)]; omega
  have hval : collatzStep^[8] (32 * k + 11) = 27 * k + 10 := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq,
      h1, h2, h3, h4, h5, h6, h7, h8]
  rw [hk, hval]
  omega

lemma descent_mod32_23 {n : ℕ} (h : n % 32 = 23) :
    collatzStep^[8] n < n := by
  have hk : n = 32 * (n / 32) + 23 := by omega
  set k := n / 32
  have h1 : collatzStep (32 * k + 23) = 96 * k + 70 := by
    rw [collatzStep_odd (by omega)]; omega
  have h2 : collatzStep (96 * k + 70) = 48 * k + 35 := by
    rw [collatzStep_even (by omega)]; omega
  have h3 : collatzStep (48 * k + 35) = 144 * k + 106 := by
    rw [collatzStep_odd (by omega)]; omega
  have h4 : collatzStep (144 * k + 106) = 72 * k + 53 := by
    rw [collatzStep_even (by omega)]; omega
  have h5 : collatzStep (72 * k + 53) = 216 * k + 160 := by
    rw [collatzStep_odd (by omega)]; omega
  have h6 : collatzStep (216 * k + 160) = 108 * k + 80 := by
    rw [collatzStep_even (by omega)]; omega
  have h7 : collatzStep (108 * k + 80) = 54 * k + 40 := by
    rw [collatzStep_even (by omega)]; omega
  have h8 : collatzStep (54 * k + 40) = 27 * k + 20 := by
    rw [collatzStep_even (by omega)]; omega
  have hval : collatzStep^[8] (32 * k + 23) = 27 * k + 20 := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq,
      h1, h2, h3, h4, h5, h6, h7, h8]
  rw [hk, hval]
  omega

lemma coalesce_mod6_5 {n : ℕ} (h : n % 6 = 5) :
    ∃ m : ℕ, 0 < m ∧ m < n ∧ collatzStep^[2] m = n ∧ m ≠ 1 ∧ collatzStep m ≠ 1 := by
  have hk : n = 6 * (n / 6) + 5 := by omega
  set k := n / 6
  refine ⟨4 * k + 3, by omega, by omega, ?_, by omega, ?_⟩
  · have h1 : collatzStep (4 * k + 3) = 12 * k + 10 := by
      rw [collatzStep_odd (by omega)]; omega
    have h2 : collatzStep (12 * k + 10) = 6 * k + 5 := by
      rw [collatzStep_even (by omega)]; omega
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq, h1, h2]
    omega
  · rw [collatzStep_odd (by omega)]
    omega

lemma prefix_bound (n m : ℕ) (hge : ∀ t ≤ m, n ≤ collatzStep^[t] n) :
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
        _ ≤ 2 ^ e * n ^ o * ((3 * n + 1) * collatzStep^[m] n) :=
            Nat.mul_le_mul_left _ hmul_step
        _ = (3 * n + 1) * (2 ^ e * n ^ o * collatzStep^[m] n) := by ring
        _ ≤ (3 * n + 1) * ((3 * n + 1) ^ o * n) := Nat.mul_le_mul_left _ ih'
        _ = (3 * n + 1) ^ (o + 1) * n := by rw [pow_succ]; ring

lemma descent_of_ratio {n m : ℕ} (hn : 1000 ≤ n)
    (hratio :
      3001 ^ ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card <
      2 ^ ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card *
        1000 ^ ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card) :
    ∃ t : ℕ, collatzStep^[t] n < n := by
  by_contra! hge
  set e := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 0)).card
  set o := ((Finset.range m).filter (fun i => collatzStep^[i] n % 2 = 1)).card
  have hpb := prefix_bound n m (fun t _ => hge t)
  have hge_m : n ≤ collatzStep^[m] n := hge m
  have hstep1 : 2 ^ e * n ^ o * n ≤ (3 * n + 1) ^ o * n :=
    le_trans (Nat.mul_le_mul_left _ hge_m) hpb
  have hstep2 : 2 ^ e * n ^ o ≤ (3 * n + 1) ^ o :=
    Nat.le_of_mul_le_mul_right hstep1 (by omega : 0 < n)
  have hlin : 1000 * (3 * n + 1) ≤ 3001 * n := by omega
  have hpow : (1000 * (3 * n + 1)) ^ o ≤ (3001 * n) ^ o := Nat.pow_le_pow_left hlin o
  have hstep3 : 2 ^ e * 1000 ^ o * n ^ o ≤ 3001 ^ o * n ^ o := calc
    2 ^ e * 1000 ^ o * n ^ o
        = 1000 ^ o * (2 ^ e * n ^ o) := by ring
    _ ≤ 1000 ^ o * (3 * n + 1) ^ o := Nat.mul_le_mul_left _ hstep2
    _ = (1000 * (3 * n + 1)) ^ o := by rw [mul_pow]
    _ ≤ (3001 * n) ^ o := hpow
    _ = 3001 ^ o * n ^ o := by rw [mul_pow]
  have hnpos : 0 < n ^ o := Nat.pow_pos (by omega)
  have hstep4 : 2 ^ e * 1000 ^ o ≤ 3001 ^ o :=
    Nat.le_of_mul_le_mul_right hstep3 hnpos
  omega

theorem main : H1 → H2 → type_of% @CollatzConjecture.collatz_conjecture := by
  intro h1 h2 n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hsmall : n < 1000
    · exact h1 n hn hsmall
    · have hge1000 : 1000 ≤ n := by omega
      have hgt1 : 1 < n := by omega
      by_cases h2m : n % 2 = 0
      · have hlt := descent_even hgt1 h2m
        obtain ⟨r, hr⟩ := ih (collatzStep^[1] n) hlt (iterate_pos hn 1)
        exact ⟨r + 1, by rw [Function.iterate_add_apply, hr]⟩
      · by_cases h4 : n % 4 = 1
        · have hlt := descent_mod4_1 hgt1 h4
          obtain ⟨r, hr⟩ := ih (collatzStep^[3] n) hlt (iterate_pos hn 3)
          exact ⟨r + 3, by rw [Function.iterate_add_apply, hr]⟩
        · by_cases h16 : n % 16 = 3
          · have hlt := descent_mod16_3 h16
            obtain ⟨r, hr⟩ := ih (collatzStep^[6] n) hlt (iterate_pos hn 6)
            exact ⟨r + 6, by rw [Function.iterate_add_apply, hr]⟩
          · by_cases h32a : n % 32 = 11
            · have hlt := descent_mod32_11 h32a
              obtain ⟨r, hr⟩ := ih (collatzStep^[8] n) hlt (iterate_pos hn 8)
              exact ⟨r + 8, by rw [Function.iterate_add_apply, hr]⟩
            · by_cases h32b : n % 32 = 23
              · have hlt := descent_mod32_23 h32b
                obtain ⟨r, hr⟩ := ih (collatzStep^[8] n) hlt (iterate_pos hn 8)
                exact ⟨r + 8, by rw [Function.iterate_add_apply, hr]⟩
              · by_cases h3 : n % 3 = 2
                · have h6 : n % 6 = 5 := by omega
                  obtain ⟨m, hmpos, hmlt, hmeq, hm1, hm2⟩ := coalesce_mod6_5 h6
                  obtain ⟨t, ht⟩ := ih m hmlt hmpos
                  have ht2 : 2 ≤ t := by
                    by_contra! hlt2
                    interval_cases t
                    · simp at ht; exact hm1 ht
                    · simp at ht; exact hm2 ht
                  refine ⟨t - 2, ?_⟩
                  rw [← hmeq, ← Function.iterate_add_apply, Nat.sub_add_cancel ht2, ht]
                · have hsurv : n % 32 = 7 ∨ n % 32 = 15 ∨ n % 32 = 27 ∨ n % 32 = 31 := by omega
                  obtain ⟨m, hm⟩ := h2 n hge1000 hsurv h3
                  obtain ⟨t, ht⟩ := descent_of_ratio hge1000 hm
                  obtain ⟨r, hr⟩ := ih (collatzStep^[t] n) ht (iterate_pos hn t)
                  exact ⟨r + t, by rw [Function.iterate_add_apply, hr]⟩

end OMA.R_CollatzConjecture_collatz_conjecture_R2
