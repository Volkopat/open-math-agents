import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1

-- Reduction CollatzConjecture.collatz_conjecture.R1.H1.R1 of step CollatzConjecture.collatz_conjecture.R1.H1
-- Credit: @Twalways

/-!
# Boundedness of Collatz trajectories via tail-minimum escape, Terras contraction, and paradoxical obstruction

Unlike the cycle case (`R1.H2`), an unbounded Collatz trajectory cannot have a finite liminf:
any repeated visit below a fixed bound `M` produces an eventual repeat by pigeonhole and hence
an eventually periodic (bounded) trajectory. Consequently, `main` proves inside Lean without
any finite base verification:

1. **Pigeonhole escape**: every unbounded trajectory diverges to infinity
   (`∀ M, ∃ m₀, ∀ m ≥ m₀, M ≤ collatzStep^[m] n`).
2. **Well-ordering tail minimum**: for EVERY cutoff `M`, any unbounded trajectory contains a
   never-descending divergent seed `y ≥ M` (`∀ t, y ≤ collatzStep^[t] y` and
   `∀ B, ∃ t, B < collatzStep^[t] y`).
3. **Mod-128 stopping-time sieve**: every never-descending seed `y ≥ 10000` survives all
   short stopping-time congruences (`0 mod 2`, `1 mod 4`, `3 mod 16`, `11 mod 32`, `23 mod 32`,
   `7 mod 128`, `15 mod 128`, `59 mod 128`), leaving only 13 residue classes mod 128.
4. **Exact multiplicative prefix bound**: along any non-descending prefix of length `t`,
   `2 ^ e * y ^ o ≤ (3 * y + 1) ^ o`.

This splits `R1.H1` cleanly into two genuinely distinct mathematical statements:

* `H1` (eventual Terras contraction): every never-descending divergent trajectory starting at
  `n ≥ 10000` in the 13 surviving mod-128 classes eventually reaches a step `t` with `3 ^ o < 2 ^ e`.
* `H2` (no arbitrarily large paradoxical non-descending contraction, cf. Rozier-Terracol):
  there exists a cutoff `M ≥ 10000` above which no finite non-descending prefix `(n, t)` in
  the 13 surviving mod-128 classes satisfies both `3 ^ o < 2 ^ e` and `2 ^ e * n ^ o ≤ (3 * n + 1) ^ o`.
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1

open CollatzConjecture

/-- Eventual Terras contraction: every never-descending divergent orbit starting at `n ≥ 10000`
in the 13 surviving residue classes modulo 128 eventually reaches a prefix with `3 ^ o < 2 ^ e`. -/
def H1 : Prop :=
  ∀ n : ℕ, 10000 ≤ n →
    (n % 128 = 27 ∨ n % 128 = 31 ∨ n % 128 = 39 ∨ n % 128 = 47 ∨
     n % 128 = 63 ∨ n % 128 = 71 ∨ n % 128 = 79 ∨ n % 128 = 91 ∨
     n % 128 = 95 ∨ n % 128 = 103 ∨ n % 128 = 111 ∨ n % 128 = 123 ∨ n % 128 = 127) →
    (∀ t : ℕ, n ≤ collatzStep^[t] n) →
    (∀ B : ℕ, ∃ t : ℕ, B < collatzStep^[t] n) →
    ∃ t : ℕ,
      3 ^ ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card <
      2 ^ ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card

/-- No arbitrarily large paradoxical non-descending contraction: there exists a cutoff `M ≥ 10000`
such that no finite non-descending prefix `(n, t)` with `n ≥ M` in the 13 surviving mod-128
classes satisfies both `3 ^ o < 2 ^ e` and `2 ^ e * n ^ o ≤ (3 * n + 1) ^ o`. -/
def H2 : Prop :=
  ∃ M : ℕ, 10000 ≤ M ∧
    ∀ n t : ℕ, M ≤ n →
      (n % 128 = 27 ∨ n % 128 = 31 ∨ n % 128 = 39 ∨ n % 128 = 47 ∨
       n % 128 = 63 ∨ n % 128 = 71 ∨ n % 128 = 79 ∨ n % 128 = 91 ∨
       n % 128 = 95 ∨ n % 128 = 103 ∨ n % 128 = 111 ∨ n % 128 = 123 ∨ n % 128 = 127) →
      (∀ s ≤ t, n ≤ collatzStep^[s] n) →
      let e := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 0)).card
      let o := ((Finset.range t).filter (fun i => collatzStep^[i] n % 2 = 1)).card
      3 ^ o < 2 ^ e →
      2 ^ e * n ^ o ≤ (3 * n + 1) ^ o →
      False

lemma collatzStep_even {n : ℕ} (h : n % 2 = 0) : collatzStep n = n / 2 := by
  have he : Even n := Nat.even_iff.mpr h
  simp [collatzStep, he]

lemma collatzStep_odd {n : ℕ} (h : n % 2 = 1) : collatzStep n = 3 * n + 1 := by
  have ho : ¬ Even n := by
    rw [Nat.even_iff]
    omega
  simp [collatzStep, ho]

lemma iter_mod {x p : ℕ} (hp : collatzStep^[p] x = x) (m : ℕ) :
    collatzStep^[m] x = collatzStep^[m % p] x := by
  conv_lhs => rw [← Nat.mod_add_div m p]
  rw [Function.iterate_add_apply]
  congr 1
  induction m / p with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, Function.iterate_add_apply, hp, ih]

lemma bounded_of_repeat {n i j : ℕ} (hij : i < j) (heq : collatzStep^[i] n = collatzStep^[j] n) :
    ∃ B : ℕ, ∀ m : ℕ, collatzStep^[m] n ≤ B := by
  refine ⟨(Finset.range j).sup (fun r => collatzStep^[r] n), ?_⟩
  intro m
  by_cases hmj : m < j
  · exact Finset.le_sup (f := fun r => collatzStep^[r] n) (Finset.mem_range.mpr hmj)
  · set p := j - i
    have hp_pos : 0 < p := by omega
    have hper : collatzStep^[p] (collatzStep^[i] n) = collatzStep^[i] n := by
      rw [← Function.iterate_add_apply, show p + i = j by omega]
      exact heq.symm
    have hm_eq : collatzStep^[m] n = collatzStep^[(m - i) % p + i] n := by
      have hm1 : m = (m - i) + i := by omega
      conv_lhs => rw [hm1, Function.iterate_add_apply]
      rw [iter_mod hper (m - i), ← Function.iterate_add_apply]
    have hlt : (m - i) % p + i < j := by
      have := Nat.mod_lt (m - i) hp_pos
      omega
    rw [hm_eq]
    exact Finset.le_sup (f := fun r => collatzStep^[r] n) (Finset.mem_range.mpr hlt)

lemma escape_of_unbounded {n : ℕ} (hunb : ∀ B : ℕ, ∃ m : ℕ, B < collatzStep^[m] n) (M : ℕ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → M ≤ collatzStep^[m] n := by
  by_contra! hinf
  classical
  let g : ℕ → ℕ := fun a => Classical.choose (hinf a)
  have hg_ge : ∀ a, a ≤ g a := fun a => (Classical.choose_spec (hinf a)).1
  have hg_lt : ∀ a, collatzStep^[g a] n < M := fun a => (Classical.choose_spec (hinf a)).2
  let f : ℕ → ℕ := Nat.rec (g 0) (fun _ prev => g (prev + 1))
  have hf_succ : ∀ k, f k < f (k + 1) := by
    intro k
    have h1 : f k + 1 ≤ g (f k + 1) := hg_ge (f k + 1)
    change f k < g (f k + 1)
    omega
  have hf_strict : StrictMono f := strictMono_nat_of_lt_succ hf_succ
  have hf_lt : ∀ k, collatzStep^[f k] n < M := by
    intro k
    cases k with
    | zero => exact hg_lt 0
    | succ k => exact hg_lt (f k + 1)
  have hmaps : ∀ k ∈ Finset.range (M + 1), collatzStep^[f k] n ∈ Finset.range M := by
    intro k _
    exact Finset.mem_range.mpr (hf_lt k)
  have hcard : (Finset.range M).card < (Finset.range (M + 1)).card := by simp
  obtain ⟨a, _, b, _, hab, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hbdd : ∃ B : ℕ, ∀ m : ℕ, collatzStep^[m] n ≤ B := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact bounded_of_repeat (hf_strict h) heq
    · exact bounded_of_repeat (hf_strict h) heq.symm
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨m, hm⟩ := hunb B
  exact not_lt_of_ge (hB m) hm

lemma exists_tail_min {n : ℕ} (hunb : ∀ B : ℕ, ∃ m : ℕ, B < collatzStep^[m] n) (M : ℕ) :
    ∃ y : ℕ, M ≤ y ∧ (∀ t : ℕ, y ≤ collatzStep^[t] y) ∧ (∀ B : ℕ, ∃ t : ℕ, B < collatzStep^[t] y) := by
  classical
  obtain ⟨m₀, hm₀⟩ := escape_of_unbounded hunb M
  have hne : ∃ v : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ collatzStep^[m] n = v :=
    ⟨collatzStep^[m₀] n, m₀, le_refl m₀, rfl⟩
  set y := Nat.find hne
  obtain ⟨m₁, hm₁, hmy⟩ := Nat.find_spec hne
  change collatzStep^[m₁] n = y at hmy
  refine ⟨y, ?_, ?_, ?_⟩
  · rw [← hmy]
    exact hm₀ m₁ hm₁
  · intro t
    by_contra! hlt
    have hmem : ∃ m : ℕ, m₀ ≤ m ∧ collatzStep^[m] n = collatzStep^[t] y := by
      refine ⟨t + m₁, by omega, ?_⟩
      rw [Function.iterate_add_apply, hmy]
    exact Nat.find_min hne hlt hmem
  · intro B
    set B' := max B ((Finset.range m₁).sup (fun r => collatzStep^[r] n))
    obtain ⟨m, hm⟩ := hunb B'
    have hm_ge : m₁ ≤ m := by
      by_contra! hlt
      have hle : collatzStep^[m] n ≤ (Finset.range m₁).sup (fun r => collatzStep^[r] n) :=
        Finset.le_sup (f := fun r => collatzStep^[r] n) (Finset.mem_range.mpr hlt)
      have hle' : collatzStep^[m] n ≤ B' := le_trans hle (le_max_right _ _)
      omega
    refine ⟨m - m₁, ?_⟩
    have heq : collatzStep^[m - m₁] y = collatzStep^[m] n := by
      rw [← hmy, ← Function.iterate_add_apply, Nat.sub_add_cancel hm_ge]
    rw [heq]
    exact lt_of_le_of_lt (le_max_left _ _) hm

lemma descent_even {n : ℕ} (hn : 1 < n) (h : n % 2 = 0) : collatzStep^[1] n < n := by
  simp only [Function.iterate_one, collatzStep_even h]
  omega

lemma descent_mod4_1 {n : ℕ} (hn : 1 < n) (h : n % 4 = 1) : collatzStep^[3] n < n := by
  have hk : n = 4 * (n / 4) + 1 := by omega
  set k := n / 4
  have h1 : collatzStep (4 * k + 1) = 12 * k + 4 := by rw [collatzStep_odd (by omega)]; omega
  have h2 : collatzStep (12 * k + 4) = 6 * k + 2 := by rw [collatzStep_even (by omega)]; omega
  have h3 : collatzStep (6 * k + 2) = 3 * k + 1 := by rw [collatzStep_even (by omega)]; omega
  have hval : collatzStep^[3] (4 * k + 1) = 3 * k + 1 := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq, h1, h2, h3]
  rw [hk, hval]
  omega

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

lemma mod128_of_never_descends {y : ℕ} (hy : 1 < y) (hmin : ∀ t : ℕ, y ≤ collatzStep^[t] y) :
    y % 128 = 27 ∨ y % 128 = 31 ∨ y % 128 = 39 ∨ y % 128 = 47 ∨
    y % 128 = 63 ∨ y % 128 = 71 ∨ y % 128 = 79 ∨ y % 128 = 91 ∨
    y % 128 = 95 ∨ y % 128 = 103 ∨ y % 128 = 111 ∨ y % 128 = 123 ∨ y % 128 = 127 := by
  have h2 : y % 2 ≠ 0 := fun h => not_lt_of_ge (hmin 1) (descent_even hy h)
  have h4 : y % 4 ≠ 1 := fun h => not_lt_of_ge (hmin 3) (descent_mod4_1 hy h)
  have h16 : y % 16 ≠ 3 := fun h => not_lt_of_ge (hmin 6) (descent_mod16_3 h)
  have h32a : y % 32 ≠ 11 := fun h => not_lt_of_ge (hmin 8) (descent_mod32_11 h)
  have h32b : y % 32 ≠ 23 := fun h => not_lt_of_ge (hmin 8) (descent_mod32_23 h)
  have h128a : y % 128 ≠ 7 := fun h => not_lt_of_ge (hmin 11) (descent_mod128_7 h)
  have h128b : y % 128 ≠ 15 := fun h => not_lt_of_ge (hmin 11) (descent_mod128_15 h)
  have h128c : y % 128 ≠ 59 := fun h => not_lt_of_ge (hmin 11) (descent_mod128_59 h)
  omega

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

theorem main : H1 → H2 → OMA.R_CollatzConjecture_collatz_conjecture_R1.H1 := by
  intro h1 h2 n _
  obtain ⟨M, hM10000, hM⟩ := h2
  by_contra! hunb
  obtain ⟨y, hMy, hymin, hyunb⟩ := exists_tail_min hunb M
  have hy10000 : 10000 ≤ y := le_trans hM10000 hMy
  have hsurv := mod128_of_never_descends (by omega) hymin
  obtain ⟨t, ht⟩ := h1 y hy10000 hsurv hymin hyunb
  have hpb := upper_prefix_bound y t (fun s _ => hymin s)
  have hyt : y ≤ collatzStep^[t] y := hymin t
  have hstep1 :
      2 ^ ((Finset.range t).filter (fun i => collatzStep^[i] y % 2 = 0)).card *
        y ^ ((Finset.range t).filter (fun i => collatzStep^[i] y % 2 = 1)).card * y ≤
      (3 * y + 1) ^ ((Finset.range t).filter (fun i => collatzStep^[i] y % 2 = 1)).card * y :=
    le_trans (Nat.mul_le_mul_left _ hyt) hpb
  have hup :
      2 ^ ((Finset.range t).filter (fun i => collatzStep^[i] y % 2 = 0)).card *
        y ^ ((Finset.range t).filter (fun i => collatzStep^[i] y % 2 = 1)).card ≤
      (3 * y + 1) ^ ((Finset.range t).filter (fun i => collatzStep^[i] y % 2 = 1)).card :=
    Nat.le_of_mul_le_mul_right hstep1 (by omega : 0 < y)
  exact hM y t hMy hsurv (fun s _ => hymin s) ht hup

end OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1
