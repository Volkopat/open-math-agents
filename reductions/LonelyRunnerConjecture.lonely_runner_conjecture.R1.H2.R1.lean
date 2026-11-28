import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.GCDMonoid.Finset

/-!
Reduction `LonelyRunnerConjecture.lonely_runner_conjecture.R1.H2.R1` of step `R1.H2`
(`3 ≤ k ≤ 7` moving integer runners, i.e., `4 ≤ n ≤ 8` total runners).

Unconditionally proved in-file (eliminating all unbounded families and solving `k = 3, 4` outright):
1. `k = 3` (`4` runners, Betke-Wills 1972) and `k = 4` (`5` runners, Bohman-Holzman-Kleitman 2001 /
   Barajas-Serra 2008) for all unbounded integer velocity tuples, eliminating `k = 3` and `k = 4`
   completely.
2. Malikiosis-Santos-Schymura (2025) zonotopal subset-GCD sum bound
   `∑_{∅ ≠ S ⊆ Fin k} S.gcd w ≤ C(k + 1, 2) ^ (k - 1)` for `k = 5, 6, 7`, reducing all remaining
   regimes to finite bounded-velocity search spaces.
3. Rosenfeld's `(k - 1)`-subset coprimality sieve (`∀ i₀, (Finset.univ.erase i₀).gcd w = 1`) and
   small-divisor sieve (`∀ j ∈ [2, k + 1], ∃ i, j ∣ w i`).
4. Generalized prime-multiplicity shift sieve proving that for every `k ≥ 5` and every odd prime
   `q ≥ 3`, at most `k - 3` speeds are divisible by `q` (and for `k ≥ 7` and prime `q ≥ 7`, at most
   `k - 4` speeds are divisible by `q`).
5. Barajas-Serra (2008) `p`-adic prime-filtering theorem for all odd primes `p`, applied at
   `k = 6, p = 7` to prove unconditionally that at most `2` speeds are divisible by `7`.

Remaining finite bounded-zonotope regimes:
- `H1`: Six lonely runners (`k = 5`, Cusick-Pomerance 1984 / Bohman-Holzman-Kleitman 2001) on
  sieved tuples with subset-GCD sum `≤ 15 ^ 4`.
- `H2`: Seven lonely runners (`k = 6`, Barajas-Serra 2008) on prime-filtered tuples with `1` or `2`
  multiples of `7` and subset-GCD sum `≤ 21 ^ 5`.
- `H3`: Eight lonely runners (`k = 7`, Rosenfeld 2025) on prime-sieved tuples with subset-GCD sum
  `≤ 28 ^ 6`.

Credit: @paynebrowning
-/

namespace OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1_H2_R1

-- Bounded, maximally-sieved 6-runner integer regime (k = 5).
def H1 : Prop :=
  ∀ (w : Fin 5 → ℕ),
    (∀ i : Fin 5, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∀ i₀ : Fin 5, (Finset.univ.erase i₀).gcd w = 1) →
    (∀ j : ℕ, 2 ≤ j → j ≤ 6 → ∃ i : Fin 5, j ∣ w i) →
    (∀ q : ℕ, Nat.Prime q → 3 ≤ q → (Finset.univ.filter (fun i : Fin 5 => q ∣ w i)).card ≤ 2) →
    (∃ i j : Fin 5, i.val + 1 = j.val ∧ j.val + 1 < 5 ∧ (5 - 1) * w j < 2 * 5 * w i) →
    (∑ S ∈ (Finset.univ : Finset (Fin 5)).powerset.erase ∅, S.gcd w) ≤ (Nat.choose 6 2) ^ 4 →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 5, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((5 + 1 : ℕ) : ℝ)

-- Bounded, prime-filtered 7-runner integer regime (k = 6, with 1 or 2 multiples of 7).
def H2 : Prop :=
  ∀ (w : Fin 6 → ℕ),
    (∀ i : Fin 6, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∀ i₀ : Fin 6, (Finset.univ.erase i₀).gcd w = 1) →
    (∀ j : ℕ, 2 ≤ j → j ≤ 7 → ∃ i : Fin 6, j ∣ w i) →
    (∀ q : ℕ, Nat.Prime q → 3 ≤ q → (Finset.univ.filter (fun i : Fin 6 => q ∣ w i)).card ≤ 3) →
    (Finset.univ.filter (fun i : Fin 6 => 7 ∣ w i)).card ≤ 2 →
    (∃ i j : Fin 6, i.val + 1 = j.val ∧ j.val + 1 < 6 ∧ (6 - 1) * w j < 2 * 6 * w i) →
    (∑ S ∈ (Finset.univ : Finset (Fin 6)).powerset.erase ∅, S.gcd w) ≤ (Nat.choose 7 2) ^ 5 →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 6, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((6 + 1 : ℕ) : ℝ)

-- Bounded, prime-sieved 8-runner integer regime (k = 7).
def H3 : Prop :=
  ∀ (w : Fin 7 → ℕ),
    (∀ i : Fin 7, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∀ i₀ : Fin 7, (Finset.univ.erase i₀).gcd w = 1) →
    (∀ j : ℕ, 2 ≤ j → j ≤ 8 → ∃ i : Fin 7, j ∣ w i) →
    (∀ q : ℕ, Nat.Prime q → 3 ≤ q → (Finset.univ.filter (fun i : Fin 7 => q ∣ w i)).card ≤ 4) →
    (∀ q : ℕ, Nat.Prime q → 7 ≤ q → (Finset.univ.filter (fun i : Fin 7 => q ∣ w i)).card ≤ 3) →
    (∃ i j : Fin 7, i.val + 1 = j.val ∧ j.val + 1 < 7 ∧ (7 - 1) * w j < 2 * 7 * w i) →
    (∑ S ∈ (Finset.univ : Finset (Fin 7)).powerset.erase ∅, S.gcd w) ≤ (Nat.choose 8 2) ^ 6 →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 7, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((7 + 1 : ℕ) : ℝ)

section ReductionProofs

noncomputable section

/- ### Module 1: UnitAddCircle & Small-Runner Base Cases (k = 1, 2, 3) -/

private lemma two_mul_choose_two (n : ℕ) : 2 * Nat.choose (n + 1) 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, mul_add, ih]
    ring

private lemma unitAddCircle_dist_neg (x : ℝ) :
    dist ((-x : ℝ) : UnitAddCircle) 0 = dist (x : UnitAddCircle) 0 := by
  rw [dist_zero_right, dist_zero_right, QuotientAddGroup.mk_neg, norm_neg]

private lemma unitAddCircle_dist_abs_single (x : ℝ) :
    dist ((|x| : ℝ) : UnitAddCircle) 0 = dist (x : UnitAddCircle) 0 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, unitAddCircle_dist_neg]

private lemma unitAddCircle_dist_eq_abs_of_lt_half {x : ℝ} (hx : |x| < 1 / 2) :
    dist (x : UnitAddCircle) 0 = |x| := by
  rw [dist_zero_right, UnitAddCircle.norm_eq]
  have hround_zero : round x = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(round x : ℝ)| := by
      have hint : (1 : ℤ) ≤ |round x| := Int.one_le_abs hne
      exact_mod_cast hint
    have h2 : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
    have h3 : |(round x : ℝ)| ≤ |x - (round x : ℝ)| + |x| := by
      calc
        |(round x : ℝ)| = |((round x : ℝ) - x) + x| := by ring_nf
        _ ≤ |(round x : ℝ) - x| + |x| := abs_add_le _ _
        _ = |x - (round x : ℝ)| + |x| := by rw [abs_sub_comm]
    linarith
  rw [hround_zero, Int.cast_zero, sub_zero]

private lemma unitAddCircle_int_cast_eq_zero (z : ℤ) :
    (((z : ℝ) : UnitAddCircle)) = 0 := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
  exact ⟨z, by simp⟩

private lemma unitAddCircle_dist_ge_of_Icc (x δ : ℝ) (k : ℤ)
    (h1 : (k : ℝ) + δ ≤ x) (h2 : x ≤ (k : ℝ) + 1 - δ) :
    dist (x : UnitAddCircle) 0 ≥ δ := by
  rw [ge_iff_le, dist_zero_right, UnitAddCircle.norm_eq]
  set m : ℤ := round x
  rcases le_or_gt m k with hmk | hkm
  · have hmk' : (m : ℝ) ≤ (k : ℝ) := Int.cast_le.mpr hmk
    have hle : δ ≤ x - (m : ℝ) := by linarith
    exact hle.trans (le_abs_self _)
  · have hkm1 : k + 1 ≤ m := Int.add_one_le_iff.mpr hkm
    have hkm' : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hkm1
    have hle : δ ≤ -(x - (m : ℝ)) := by linarith
    exact hle.trans (neg_le_abs _)

private lemma unitAddCircle_dist_ge_of_Icc_zero (x δ : ℝ)
    (h1 : δ ≤ x) (h2 : x ≤ 1 - δ) :
    dist (x : UnitAddCircle) 0 ≥ δ := by
  refine unitAddCircle_dist_ge_of_Icc x δ 0 ?_ ?_
  · simp [h1]
  · simp [h2]

private lemma exists_subinterval_dist_ge (A B δ L : ℝ)
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) (hLδ : L + 2 * δ ≤ 1) (hBA : 2 * L + 2 * δ ≤ B - A) :
    ∃ C D : ℝ, ∃ m : ℤ,
      A ≤ C ∧ D ≤ B ∧ D - C = L ∧ (m : ℝ) + δ ≤ C ∧ D ≤ (m : ℝ) + 1 - δ := by
  set k : ℤ := ⌊A⌋
  have hk1 : (k : ℝ) ≤ A := Int.floor_le A
  have hk2 : A < (k : ℝ) + 1 := Int.lt_floor_add_one A
  rcases le_or_gt A ((k : ℝ) + δ) with hA1 | hA1
  · refine ⟨(k : ℝ) + δ, (k : ℝ) + δ + L, k, hA1, ?_, by ring, le_rfl, ?_⟩
    · linarith
    · linarith
  · rcases le_or_gt (A + L) ((k : ℝ) + 1 - δ) with hA2 | hA2
    · refine ⟨A, A + L, k, le_rfl, ?_, by ring, hA1.le, hA2⟩
      linarith
    · refine ⟨(k : ℝ) + 1 + δ, (k : ℝ) + 1 + δ + L, k + 1, ?_, ?_, by ring, ?_, ?_⟩
      · linarith
      · linarith
      · push_cast; linarith
      · push_cast; linarith

private lemma lrc_pos_one (v : Fin 1 → ℝ) (hv : ∀ i : Fin 1, 0 < v i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 1, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((1 + 1 : ℕ) : ℝ) := by
  have hv0 : 0 < v 0 := hv 0
  refine ⟨1 / (2 * v 0), by positivity, fun i => ?_⟩
  have hi : i = 0 := Subsingleton.elim i 0
  rw [hi]
  have hmul : 1 / (2 * v 0) * v 0 = (1 : ℝ) / 2 := by field_simp [ne_of_gt hv0]
  rw [hmul]
  have hcast : (1 : ℝ) / ((1 + 1 : ℕ) : ℝ) = 1 / 2 := by norm_num
  rw [hcast]
  exact unitAddCircle_dist_ge_of_Icc_zero (1 / 2) (1 / 2) (by norm_num) (by norm_num)

private lemma lrc_pos_two (v : Fin 2 → ℝ) (hv : ∀ i : Fin 2, 0 < v i) (hmono : StrictMono v) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 2, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((2 + 1 : ℕ) : ℝ) := by
  have hv0 : 0 < v 0 := hv 0
  have hv1 : 0 < v 1 := hv 1
  have hv01 : v 0 < v 1 := hmono (by decide)
  have hcast : (1 : ℝ) / ((2 + 1 : ℕ) : ℝ) = 1 / 3 := by norm_num
  rw [hcast]
  rcases lt_or_ge (v 1) (2 * v 0) with hlt | hge
  · refine ⟨1 / (3 * v 0), by positivity, fun i => ?_⟩
    fin_cases i
    · change dist ((1 / (3 * v 0) * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 3
      have hmul : 1 / (3 * v 0) * v 0 = (1 : ℝ) / 3 := by field_simp [ne_of_gt hv0]
      rw [hmul]
      exact unitAddCircle_dist_ge_of_Icc_zero (1 / 3) (1 / 3) (by norm_num) (by norm_num)
    · change dist ((1 / (3 * v 0) * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 3
      have h_eq : 1 / (3 * v 0) * v 1 = v 1 / (3 * v 0) := one_div_mul_eq_div (3 * v 0) (v 1)
      rw [h_eq]
      have hlo : (1 : ℝ) / 3 ≤ v 1 / (3 * v 0) := by rw [le_div_iff₀ (by positivity)]; linarith
      have hhi : v 1 / (3 * v 0) ≤ 1 - 1 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
      exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 3) hlo hhi
  · have hlen : 2 * (0 : ℝ) + 2 * (1 / 3 : ℝ) ≤
        (2 * v 1) / (3 * v 0) - v 1 / (3 * v 0) := by
      have hsub : (2 * v 1) / (3 * v 0) - v 1 / (3 * v 0) = v 1 / (3 * v 0) := by ring
      rw [hsub, le_div_iff₀ (by positivity)]
      linarith
    obtain ⟨C, D, m, hAC, hDB, hDC, hm1, hm2⟩ :=
      exists_subinterval_dist_ge (v 1 / (3 * v 0)) ((2 * v 1) / (3 * v 0)) (1 / 3) 0
        (by norm_num) le_rfl (by norm_num) hlen
    have hCD : C = D := by linarith
    refine ⟨C / v 1, le_div_iff₀ hv1 |>.mpr (by linarith [show (0 : ℝ) ≤ v 1 / (3 * v 0) by positivity]), fun i => ?_⟩
    fin_cases i
    · change dist ((C / v 1 * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 3
      have h1 : v 1 ≤ C * (3 * v 0) := (div_le_iff₀ (by positivity)).mp hAC
      have h2 : C * (3 * v 0) ≤ 2 * v 1 := (le_div_iff₀ (by positivity)).mp (hCD.symm ▸ hDB)
      rw [div_mul_eq_mul_div C (v 1) (v 0)]
      have hlo : (1 : ℝ) / 3 ≤ (C * v 0) / v 1 := by rw [le_div_iff₀ hv1]; linarith
      have hhi : (C * v 0) / v 1 ≤ 1 - 1 / 3 := by rw [div_le_iff₀ hv1]; linarith
      exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 3) hlo hhi
    · change dist ((C / v 1 * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 3
      rw [div_mul_cancel₀ C (ne_of_gt hv1)]
      exact unitAddCircle_dist_ge_of_Icc C (1 / 3) m hm1 (hCD ▸ hm2)

private lemma lrc_lacunary (k : ℕ) (hk : 3 ≤ k) (v : Fin k → ℝ)
    (hv_pos : ∀ i : Fin k, 0 < v i) (hv_mono : StrictMono v)
    (hlac : ∀ i j : Fin k, i.val + 1 = j.val → j.val + 1 < k →
      ((k : ℝ) - 1) * v j ≥ 2 * (k : ℝ) * v i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  let δ : ℝ := 1 / ((k + 1 : ℕ) : ℝ)
  let L : ℝ := ((k : ℝ) - 1) / ((k + 1 : ℕ) : ℝ)
  have hk_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hδ_nonneg : 0 ≤ δ := by positivity
  have hL_nonneg : 0 ≤ L := by
    refine div_nonneg ?_ hk_pos.le
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  have hLδ_sum : L + 2 * δ ≤ 1 := by
    have heq : L + 2 * δ = 1 := by dsimp [L, δ]; push_cast; field_simp [ne_of_gt hk_pos]; ring
    exact heq.le
  have h_nested : ∀ (j : ℕ) (hj : j + 1 < k),
      ∃ a b : ℝ, 0 ≤ a ∧
        b - a = L / v ⟨j, by omega⟩ ∧
        ∀ (m : Fin k), m.val ≤ j → ∀ t : ℝ, a ≤ t → t ≤ b →
          dist ((t * v m : ℝ) : UnitAddCircle) 0 ≥ δ := by
    intro j
    induction j with
    | zero =>
      intro hj
      let i0 : Fin k := ⟨0, by omega⟩
      have hv0 : 0 < v i0 := hv_pos i0
      refine ⟨δ / v i0, (1 - δ) / v i0, by positivity, ?_, ?_⟩
      · have h1 : (1 - δ) / v i0 - δ / v i0 = (1 - 2 * δ) / v i0 := by ring
        rw [h1]; congr 1; dsimp [L, δ]; push_cast; field_simp [ne_of_gt hk_pos]; ring
      · intro m hm t hta htb
        have hm_eq : m = i0 := Fin.ext (by dsimp [i0]; omega)
        rw [hm_eq]
        have hlo : δ ≤ t * v i0 := by have := (div_le_iff₀ hv0).mp hta; linarith
        have hhi : t * v i0 ≤ 1 - δ := by have := (le_div_iff₀ hv0).mp htb; linarith
        exact unitAddCircle_dist_ge_of_Icc_zero (t * v i0) δ hlo hhi
    | succ j ih =>
      intro hj_succ
      obtain ⟨a, b, ha0, hba, h_safe⟩ := ih (by omega)
      let ij : Fin k := ⟨j, by omega⟩
      let ij1 : Fin k := ⟨j + 1, by omega⟩
      have hvj : 0 < v ij := hv_pos ij
      have hvj1 : 0 < v ij1 := hv_pos ij1
      have hlac_step : ((k : ℝ) - 1) * v ij1 ≥ 2 * (k : ℝ) * v ij := hlac ij ij1 rfl hj_succ
      have hBA : 2 * L + 2 * δ ≤ v ij1 * b - v ij1 * a := by
        have h1 : v ij1 * b - v ij1 * a = v ij1 * (L / v ij) := by rw [← mul_sub, hba]
        have h2 : 2 * L + 2 * δ = (2 * (k : ℝ)) / ((k + 1 : ℕ) : ℝ) := by
          dsimp [L, δ]; push_cast; field_simp [ne_of_gt hk_pos]; ring
        have h3 : v ij1 * (L / v ij) = (((k : ℝ) - 1) * v ij1) / (((k + 1 : ℕ) : ℝ) * v ij) := by
          dsimp [L]; ring
        rw [h1, h2, h3, div_le_div_iff₀ hk_pos (by positivity)]
        nlinarith
      obtain ⟨C, D, z, hAC, hDB, hDC, hz1, hz2⟩ :=
        exists_subinterval_dist_ge (v ij1 * a) (v ij1 * b) δ L hδ_nonneg hL_nonneg hLδ_sum hBA
      have ha_le : a ≤ C / v ij1 := (le_div_iff₀ hvj1).mpr (by linarith)
      have hb_le : D / v ij1 ≤ b := (div_le_iff₀ hvj1).mpr (by linarith)
      refine ⟨C / v ij1, D / v ij1, le_trans ha0 ha_le, ?_, ?_⟩
      · rw [← sub_div, hDC]
      · intro m hm t hta htb
        rcases Nat.of_le_succ hm with hm_le | hm_eq
        · exact h_safe m hm_le t (le_trans ha_le hta) (le_trans htb hb_le)
        · have hm_fin : m = ij1 := Fin.ext hm_eq
          rw [hm_fin]
          have hCt : C ≤ t * v ij1 := (div_le_iff₀ hvj1).mp hta
          have htD : t * v ij1 ≤ D := (le_div_iff₀ hvj1).mp htb
          exact unitAddCircle_dist_ge_of_Icc (t * v ij1) δ z (le_trans hz1 hCt) (le_trans htD hz2)
  obtain ⟨a, b, ha0, hba, h_safe⟩ := h_nested (k - 2) (by omega)
  let iprev : Fin k := ⟨k - 2, by omega⟩
  let ilast : Fin k := ⟨k - 1, by omega⟩
  have hv_prev : 0 < v iprev := hv_pos iprev
  have hv_last : 0 < v ilast := hv_pos ilast
  have hv_lt : v iprev < v ilast := hv_mono (by rw [Fin.lt_def]; dsimp [iprev, ilast]; omega)
  have h2δ_le_1 : 0 + 2 * δ ≤ 1 := by linarith
  have hBA_last : 2 * (0 : ℝ) + 2 * δ ≤ v ilast * b - v ilast * a := by
    have h1 : v ilast * b - v ilast * a = (v ilast / v iprev) * L := by rw [← mul_sub, hba]; ring
    have h_ratio : 1 ≤ v ilast / v iprev := (one_le_div hv_prev).mpr hv_lt.le
    have hL_le : 1 * L ≤ (v ilast / v iprev) * L := mul_le_mul_of_nonneg_right h_ratio hL_nonneg
    have h2δ_le_L : 2 * δ ≤ L := by
      dsimp [δ, L]; rw [mul_one_div]
      refine div_le_div_of_nonneg_right ?_ hk_pos.le
      have hk3' : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    linarith
  obtain ⟨C, D, z, hAC, hDB, hDC, hz1, hz2⟩ :=
    exists_subinterval_dist_ge (v ilast * a) (v ilast * b) δ 0 hδ_nonneg le_rfl h2δ_le_1 hBA_last
  have hCD : C = D := by linarith
  have ha_t : a ≤ C / v ilast := (le_div_iff₀ hv_last).mpr (by linarith)
  have ht_b : C / v ilast ≤ b := (div_le_iff₀ hv_last).mpr (by linarith)
  refine ⟨C / v ilast, le_trans ha0 ha_t, fun m => ?_⟩
  rcases le_or_gt m.val (k - 2) with hm_le | hm_gt
  · exact h_safe m hm_le (C / v ilast) ha_t ht_b
  · have hm_eq : m = ilast := Fin.ext (by dsimp [ilast]; omega)
    rw [hm_eq, div_mul_cancel₀ C (ne_of_gt hv_last)]
    exact unitAddCircle_dist_ge_of_Icc C δ z hz1 (hCD ▸ hz2)

private lemma lrc_pos_three (v : Fin 3 → ℝ) (hv : ∀ i : Fin 3, 0 < v i) (hmono : StrictMono v) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 3, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((3 + 1 : ℕ) : ℝ) := by
  have hv0 : 0 < v 0 := hv 0
  have hv1 : 0 < v 1 := hv 1
  have hv2 : 0 < v 2 := hv 2
  have h01 : v 0 < v 1 := hmono (by decide)
  have h12 : v 1 < v 2 := hmono (by decide)
  rcases le_or_gt (3 * v 0) (v 1) with hlac01 | hlt3
  · refine lrc_lacunary 3 (by omega) v hv hmono ?_
    intro i j hij hj_lt
    have hi0 : i = 0 := Fin.ext (by omega)
    have hj1 : j = 1 := Fin.ext (by omega)
    rw [hi0, hj1]
    push_cast
    linarith
  · have hcast : (1 : ℝ) / ((3 + 1 : ℕ) : ℝ) = 1 / 4 := by norm_num
    rw [hcast]
    rcases le_or_gt (7 * v 0) (3 * v 1) with hge7 | hlt7
    · have hlen : 2 * (0 : ℝ) + 2 * (1 / 4 : ℝ) ≤
          v 2 * (7 / (4 * v 1)) - v 2 * (5 / (4 * v 1)) := by
        have hsub : v 2 * (7 / (4 * v 1)) - v 2 * (5 / (4 * v 1)) = v 2 / (2 * v 1) := by ring
        rw [hsub, le_div_iff₀ (by positivity)]
        linarith
      obtain ⟨C, D, z, hAC, hDB, hDC, hz1, hz2⟩ :=
        exists_subinterval_dist_ge (v 2 * (5 / (4 * v 1))) (v 2 * (7 / (4 * v 1))) (1 / 4) 0
          (by norm_num) le_rfl (by norm_num) hlen
      have hCD : C = D := by linarith
      have ha_t : 5 / (4 * v 1) ≤ C / v 2 := (le_div_iff₀ hv2).mpr (by linarith)
      have ht_b : C / v 2 ≤ 7 / (4 * v 1) := (div_le_iff₀ hv2).mpr (by linarith)
      refine ⟨C / v 2, le_trans (by positivity) ha_t, fun i => ?_⟩
      fin_cases i
      · change dist ((C / v 2 * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
        have hlo : (1 : ℝ) / 4 ≤ C / v 2 * v 0 := by
          have h1 : 5 * v 0 / (4 * v 1) ≤ C / v 2 * v 0 := by
            have := mul_le_mul_of_nonneg_right ha_t hv0.le
            linarith [show 5 / (4 * v 1) * v 0 = 5 * v 0 / (4 * v 1) by ring]
          have h2 : (1 : ℝ) / 4 ≤ 5 * v 0 / (4 * v 1) := by
            rw [div_le_div_iff₀ (by norm_num) (by positivity)]
            linarith
          exact le_trans h2 h1
        have hhi : C / v 2 * v 0 ≤ 1 - 1 / 4 := by
          have h1 : C / v 2 * v 0 ≤ 7 * v 0 / (4 * v 1) := by
            have := mul_le_mul_of_nonneg_right ht_b hv0.le
            linarith [show 7 / (4 * v 1) * v 0 = 7 * v 0 / (4 * v 1) by ring]
          have h2 : 7 * v 0 / (4 * v 1) ≤ 1 - 1 / 4 := by
            rw [div_le_iff₀ (by positivity)]
            linarith
          exact le_trans h1 h2
        exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4) hlo hhi
      · change dist ((C / v 2 * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
        have hlo : ((1 : ℤ) : ℝ) + 1 / 4 ≤ C / v 2 * v 1 := by
          have := (div_le_iff₀ (by positivity)).mp ha_t
          push_cast; linarith
        have hhi : C / v 2 * v 1 ≤ ((1 : ℤ) : ℝ) + 1 - 1 / 4 := by
          have := (le_div_iff₀ (by positivity)).mp ht_b
          push_cast; linarith
        exact unitAddCircle_dist_ge_of_Icc _ (1 / 4) 1 hlo hhi
      · change dist ((C / v 2 * v 2 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
        rw [div_mul_cancel₀ C (ne_of_gt hv2)]
        exact unitAddCircle_dist_ge_of_Icc C (1 / 4) z hz1 (hCD ▸ hz2)
    · rcases le_or_gt (v 2) (3 * v 0) with hle3 | hgt3
      · refine ⟨1 / (4 * v 0), by positivity, fun i => ?_⟩
        fin_cases i
        · change dist ((1 / (4 * v 0) * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
          have hmul : 1 / (4 * v 0) * v 0 = (1 : ℝ) / 4 := by field_simp [ne_of_gt hv0]
          rw [hmul]
          exact unitAddCircle_dist_ge_of_Icc_zero (1 / 4) (1 / 4) (by norm_num) (by norm_num)
        · change dist ((1 / (4 * v 0) * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
          rw [one_div_mul_eq_div]
          exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4)
            ((div_le_div_iff₀ (by norm_num) (by positivity)).mpr (by linarith))
            ((div_le_iff₀ (by positivity)).mpr (by linarith))
        · change dist ((1 / (4 * v 0) * v 2 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
          rw [one_div_mul_eq_div]
          exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4)
            ((div_le_div_iff₀ (by norm_num) (by positivity)).mpr (by linarith))
            ((div_le_iff₀ (by positivity)).mpr (by linarith))
      · rcases le_or_gt (2 * v 0 * v 1) (v 2 * (3 * v 0 - v 1)) with hI1_long | hI1_short
        · have hlen : 2 * (0 : ℝ) + 2 * (1 / 4 : ℝ) ≤
              v 2 * (3 / (4 * v 1)) - v 2 * (1 / (4 * v 0)) := by
            have hsub : v 2 * (3 / (4 * v 1)) - v 2 * (1 / (4 * v 0)) =
                v 2 * (3 * v 0 - v 1) / (4 * v 0 * v 1) := by
              field_simp [ne_of_gt hv0, ne_of_gt hv1]
            rw [hsub, le_div_iff₀ (by positivity)]
            linarith
          obtain ⟨C, D, z, hAC, hDB, hDC, hz1, hz2⟩ :=
            exists_subinterval_dist_ge (v 2 * (1 / (4 * v 0))) (v 2 * (3 / (4 * v 1))) (1 / 4) 0
              (by norm_num) le_rfl (by norm_num) hlen
          have hCD : C = D := by linarith
          have ha_t : 1 / (4 * v 0) ≤ C / v 2 := (le_div_iff₀ hv2).mpr (by linarith)
          have ht_b : C / v 2 ≤ 3 / (4 * v 1) := (div_le_iff₀ hv2).mpr (by linarith)
          refine ⟨C / v 2, le_trans (by positivity) ha_t, fun i => ?_⟩
          fin_cases i
          · change dist ((C / v 2 * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
            have hlo : (1 : ℝ) / 4 ≤ C / v 2 * v 0 := by
              have := (div_le_iff₀ (by positivity)).mp ha_t; linarith
            have hhi : C / v 2 * v 0 ≤ 1 - 1 / 4 := by
              have h1 := mul_le_mul_of_nonneg_right ht_b hv0.le
              have h2 : 3 / (4 * v 1) * v 0 ≤ 3 / 4 := by
                rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
              linarith
            exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4) hlo hhi
          · change dist ((C / v 2 * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
            have hlo : (1 : ℝ) / 4 ≤ C / v 2 * v 1 := by
              have h1 := mul_le_mul_of_nonneg_right ha_t hv1.le
              have h2 : (1 : ℝ) / 4 ≤ 1 / (4 * v 0) * v 1 := by
                rw [one_div_mul_eq_div, div_le_div_iff₀ (by norm_num) (by positivity)]
                linarith
              exact le_trans h2 h1
            have hhi : C / v 2 * v 1 ≤ 1 - 1 / 4 := by
              have := (le_div_iff₀ (by positivity)).mp ht_b; linarith
            exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4) hlo hhi
          · change dist ((C / v 2 * v 2 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
            rw [div_mul_cancel₀ C (ne_of_gt hv2)]
            exact unitAddCircle_dist_ge_of_Icc C (1 / 4) z hz1 (hCD ▸ hz2)
        · rcases le_or_gt (5 * v 1) (3 * v 2) with hge5 | hlt5
          · rcases le_or_gt (3 * v 2) (7 * v 1) with hle7' | hgt7'
            · refine ⟨3 / (4 * v 1), by positivity, fun i => ?_⟩
              fin_cases i
              · change dist ((3 / (4 * v 1) * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
                rw [div_mul_eq_mul_div]
                exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4)
                  ((div_le_div_iff₀ (by norm_num) (by positivity)).mpr (by linarith))
                  ((div_le_iff₀ (by positivity)).mpr (by linarith))
              · change dist ((3 / (4 * v 1) * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
                have hmul : 3 / (4 * v 1) * v 1 = (3 : ℝ) / 4 := by field_simp [ne_of_gt hv1]
                rw [hmul]
                exact unitAddCircle_dist_ge_of_Icc_zero (3 / 4) (1 / 4) (by norm_num) (by norm_num)
              · change dist ((3 / (4 * v 1) * v 2 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
                rw [div_mul_eq_mul_div]
                refine unitAddCircle_dist_ge_of_Icc _ (1 / 4) 1 ?_ ?_
                · rw [le_div_iff₀ (by positivity)]; push_cast; linarith
                · rw [div_le_iff₀ (by positivity)]; push_cast; linarith
            · have hv2_lt7 : v 2 < 7 * v 0 := by nlinarith
              refine ⟨7 / (4 * v 2), by positivity, fun i => ?_⟩
              fin_cases i
              · change dist ((7 / (4 * v 2) * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
                rw [div_mul_eq_mul_div]
                exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4)
                  ((div_le_div_iff₀ (by norm_num) (by positivity)).mpr (by linarith))
                  ((div_le_iff₀ (by positivity)).mpr (by nlinarith))
              · change dist ((7 / (4 * v 2) * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
                rw [div_mul_eq_mul_div]
                exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4)
                  ((div_le_div_iff₀ (by norm_num) (by positivity)).mpr (by nlinarith))
                  ((div_le_iff₀ (by positivity)).mpr (by linarith))
              · change dist ((7 / (4 * v 2) * v 2 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
                have hmul : 7 / (4 * v 2) * v 2 = (7 : ℝ) / 4 := by field_simp [ne_of_gt hv2]
                rw [hmul]
                exact unitAddCircle_dist_ge_of_Icc (7 / 4) (1 / 4) 1
                  (by push_cast; norm_num) (by push_cast; norm_num)
          · refine ⟨9 / (4 * v 2), by positivity, fun i => ?_⟩
            fin_cases i
            · change dist ((9 / (4 * v 2) * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
              rw [div_mul_eq_mul_div]
              exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4)
                ((div_le_div_iff₀ (by norm_num) (by positivity)).mpr (by linarith))
                ((div_le_iff₀ (by positivity)).mpr (by linarith))
            · change dist ((9 / (4 * v 2) * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
              rw [div_mul_eq_mul_div]
              refine unitAddCircle_dist_ge_of_Icc _ (1 / 4) 1 ?_ ?_
              · rw [le_div_iff₀ (by positivity)]; push_cast; linarith
              · rw [div_le_iff₀ (by positivity)]; push_cast; linarith
            · change dist ((9 / (4 * v 2) * v 2 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
              have hmul : 9 / (4 * v 2) * v 2 = (9 : ℝ) / 4 := by field_simp [ne_of_gt hv2]
              rw [hmul]
              exact unitAddCircle_dist_ge_of_Icc (9 / 4) (1 / 4) 2
                (by push_cast; norm_num) (by push_cast; norm_num)

private lemma lrc_lacunary_nat (m : ℕ) (hm3 : 3 ≤ m) (u : Fin m → ℕ)
    (hu_pos : ∀ i : Fin m, 0 < u i) (hu_mono : StrictMono u)
    (h_not_nonlac : ¬ ∃ i j : Fin m, i.val + 1 = j.val ∧ j.val + 1 < m ∧
      (m - 1) * u j < 2 * m * u i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  refine lrc_lacunary m hm3 (fun i => (u i : ℝ))
    (fun i => Nat.cast_pos.mpr (hu_pos i))
    (fun i j hij => Nat.cast_lt.mpr (hu_mono hij)) ?_
  intro i j hij hj_lt
  have h_ge : 2 * m * u i ≤ (m - 1) * u j := by
    by_contra hlt; exact h_not_nonlac ⟨i, j, hij, hj_lt, Nat.lt_of_not_le hlt⟩
  have h_cast : ((2 * m * u i : ℕ) : ℝ) ≤ (((m - 1) * u j : ℕ) : ℝ) := by exact_mod_cast h_ge
  have hm_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  push_cast at h_cast; rw [hm_sub] at h_cast; exact h_cast

private lemma lrc_nat_gcd_reduction (m : ℕ) (hm : 1 ≤ m) (w : Fin m → ℕ)
    (hw_pos : ∀ i : Fin m, 0 < w i) (hw_mono : StrictMono w)
    (h_prim : ∀ (w' : Fin m → ℕ), (∀ i : Fin m, 0 < w' i) → StrictMono w' →
      Finset.univ.gcd w' = 1 →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (w' i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  let g : ℕ := Finset.univ.gcd w
  have i0_mem : (⟨0, by omega⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
  have hg_ne : g ≠ 0 := fun hg0 =>
    Nat.ne_of_gt (hw_pos ⟨0, by omega⟩) ((Finset.gcd_eq_zero_iff.mp hg0) _ i0_mem)
  let w' : Fin m → ℕ := fun i => w i / g
  have hw_mul : ∀ i : Fin m, g * w' i = w i :=
    fun i => Nat.mul_div_cancel' (Finset.gcd_dvd (Finset.mem_univ i))
  have hw'_pos : ∀ i : Fin m, 0 < w' i := by
    intro i
    rcases Nat.eq_zero_or_pos (w' i) with hw'0 | hpos
    · exfalso; exact Nat.ne_of_gt (hw_pos i) (by rw [← hw_mul i, hw'0, mul_zero])
    · exact hpos
  have hw'_mono : StrictMono w' := fun i j hij =>
    lt_of_mul_lt_mul_left' (by rw [hw_mul i, hw_mul j]; exact hw_mono hij)
  have hw'_gcd : Finset.univ.gcd w' = 1 := by
    apply Nat.dvd_one.mp
    have hdvd_g : g * Finset.univ.gcd w' ∣ g * 1 := by
      rw [mul_one]; refine Finset.dvd_gcd fun i hi => ?_
      rw [← hw_mul i]; exact mul_dvd_mul_left g (Finset.gcd_dvd hi)
    exact (mul_dvd_mul_iff_left hg_ne).mp hdvd_g
  obtain ⟨t', ht'0, ht'⟩ := h_prim w' hw'_pos hw'_mono hw'_gcd
  refine ⟨t' / (g : ℝ), by positivity, fun i => ?_⟩
  have hwi_cast : (w i : ℝ) = (g : ℝ) * (w' i : ℝ) := by exact_mod_cast (hw_mul i).symm
  have h_scale : t' / (g : ℝ) * (w i : ℝ) = t' * (w' i : ℝ) := by
    rw [hwi_cast]; field_simp [Nat.cast_ne_zero.mpr hg_ne]
  rw [h_scale]; exact ht' i

private lemma lrc_nat_one_exception_sieve (m : ℕ) (hm3 : 3 ≤ m) (w : Fin m → ℕ)
    (hw_pos : ∀ i : Fin m, 0 < w i) (hw_mono : StrictMono w)
    (hw_gcd : Finset.univ.gcd w = 1)
    (i₀ : Fin m) (h_sub_gcd : (Finset.univ.erase i₀).gcd w ≠ 1)
    (h_prev : ∀ (u : Fin (m - 1) → ℕ), (∀ l : Fin (m - 1), 0 < u l) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ l : Fin (m - 1), dist ((t * (u l : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m - 1 + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  let U : Finset (Fin m) := Finset.univ.erase i₀
  have hU_card : U.card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_fin]
  let g : ℕ := U.gcd w
  have hj_ex : ∃ j : Fin m, j ∈ U := by
    rcases eq_or_ne i₀.val 0 with hi0 | hi0
    · have hne1 : (⟨1, by omega⟩ : Fin m) ≠ i₀ := fun h => by
        have := congr_arg Fin.val h; dsimp at this; omega
      exact ⟨⟨1, by omega⟩, Finset.mem_erase.mpr ⟨hne1, Finset.mem_univ _⟩⟩
    · have hne0 : (⟨0, by omega⟩ : Fin m) ≠ i₀ := fun h => by
        have := congr_arg Fin.val h; dsimp at this; omega
      exact ⟨⟨0, by omega⟩, Finset.mem_erase.mpr ⟨hne0, Finset.mem_univ _⟩⟩
  obtain ⟨j_wit, hj_wit⟩ := hj_ex
  have hg_ne0 : g ≠ 0 := fun hg0 =>
    Nat.ne_of_gt (hw_pos j_wit) ((Finset.gcd_eq_zero_iff.mp hg0) j_wit hj_wit)
  let p : ℕ := g.minFac
  have hp_prime : Nat.Prime p := Nat.minFac_prime h_sub_gcd
  have hp2 : 2 ≤ p := hp_prime.two_le
  have hp_pos_r : (0 : ℝ) < (p : ℝ) := by positivity
  have hp_dvd_U : ∀ i ∈ U, p ∣ w i :=
    fun i hi => dvd_trans (Nat.minFac_dvd g) (Finset.gcd_dvd hi)
  have hp_ndvd_0 : ¬ p ∣ w i₀ := by
    intro hdvd0
    have hdvd_all : p ∣ Finset.univ.gcd w := by
      refine Finset.dvd_gcd fun i _ => ?_
      rcases eq_or_ne i i₀ with rfl | hne
      · exact hdvd0
      · exact hp_dvd_U i (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i⟩)
    rw [hw_gcd] at hdvd_all
    have hp1 : p ≤ 1 := Nat.le_of_dvd zero_lt_one hdvd_all
    omega
  have hcop : Nat.Coprime (w i₀) p := (hp_prime.coprime_iff_not_dvd.mpr hp_ndvd_0).symm
  let emb := U.orderEmbOfFin hU_card
  let u : Fin (m - 1) → ℕ := fun l => w (emb l) / p
  have hu_mul : ∀ l : Fin (m - 1), p * u l = w (emb l) :=
    fun l => Nat.mul_div_cancel' (hp_dvd_U (emb l) (Finset.orderEmbOfFin_mem U hU_card l))
  have hu_pos : ∀ l : Fin (m - 1), 0 < u l := by
    intro l
    rcases Nat.eq_zero_or_pos (u l) with hu0 | hpos
    · exfalso; exact Nat.ne_of_gt (hw_pos (emb l)) (by rw [← hu_mul l, hu0, mul_zero])
    · exact hpos
  have hu_mono : StrictMono u := fun l₁ l₂ hlt =>
    lt_of_mul_lt_mul_left' (by rw [hu_mul l₁, hu_mul l₂]; exact hw_mono (emb.strictMono hlt))
  obtain ⟨t', ht'0, ht'_lonely⟩ := h_prev u hu_pos hu_mono
  let α : ℝ := t' * (w i₀ : ℝ) / (p : ℝ)
  let fr : ℝ := Int.fract α
  have hfr0 : 0 ≤ fr := Int.fract_nonneg α
  have hfr1 : fr < 1 := Int.fract_lt_one α
  have hex_res : ∃ (r : ℕ) (z : ℤ), r < p ∧
      (z : ℝ) + 1 / 4 ≤ fr + (r : ℝ) / (p : ℝ) ∧
      fr + (r : ℝ) / (p : ℝ) ≤ (z : ℝ) + 1 - 1 / 4 := by
    rcases lt_or_ge fr (1 / 4) with hlt14 | hge14
    · refine ⟨p / 2, 0, Nat.div_lt_self hp_prime.pos one_lt_two, ?_, ?_⟩
      · have h1 : p ≤ 4 * (p / 2) := by omega
        have h1_cast : (p : ℝ) ≤ 4 * ((p / 2 : ℕ) : ℝ) := by exact_mod_cast h1
        have h1r : (1 : ℝ) / 4 ≤ ((p / 2 : ℕ) : ℝ) / (p : ℝ) := by
          rw [div_le_div_iff₀ (by norm_num) hp_pos_r]; linarith
        push_cast; linarith
      · have h2 : 2 * (p / 2) ≤ p := Nat.mul_div_le p 2
        have h2_cast : 2 * ((p / 2 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
        have h2r : ((p / 2 : ℕ) : ℝ) / (p : ℝ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hp_pos_r (by norm_num)]; linarith
        push_cast; linarith
    · rcases le_or_gt fr (3 / 4) with hle34 | hgt34
      · refine ⟨0, 0, hp_prime.pos, ?_, ?_⟩
        · simp only [Nat.cast_zero, Int.cast_zero, zero_div, add_zero, zero_add]; linarith
        · simp only [Nat.cast_zero, Int.cast_zero, zero_div, add_zero, zero_add]; linarith
      · refine ⟨(p + 1) / 2, 1, by omega, ?_, ?_⟩
        · have h1 : p ≤ 2 * ((p + 1) / 2) := by omega
        --
          have h1_cast : (p : ℝ) ≤ 2 * (((p + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h1
          have h1r : (1 : ℝ) / 2 ≤ (((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ) := by
            rw [div_le_div_iff₀ (by norm_num) hp_pos_r]; linarith
          push_cast; linarith
        · have h2 : 4 * ((p + 1) / 2) ≤ 3 * p := by omega
          have h2_cast : 4 * (((p + 1) / 2 : ℕ) : ℝ) ≤ 3 * (p : ℝ) := by exact_mod_cast h2
          have h2r : (((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ) ≤ 3 / 4 := by
            rw [div_le_div_iff₀ hp_pos_r (by norm_num)]; linarith
          push_cast; linarith
  obtain ⟨r, z, hr_lt, hres_lo, hres_hi⟩ := hex_res
  let mulMod : Fin p → Fin p := fun s => ⟨(s.val * w i₀) % p, Nat.mod_lt _ hp_prime.pos⟩
  have h_inj : Function.Injective mulMod := by
    intro s₁ s₂ heq
    have hmod_eq : (s₁.val * w i₀) % p = (s₂.val * w i₀) % p := congr_arg Fin.val heq
    by_contra hne
    have hval_ne : s₁.val ≠ s₂.val := fun hv => hne (Fin.ext hv)
    rcases lt_or_gt_of_ne hval_ne with hlt | hgt
    · have hdvd_sub : p ∣ (s₂.val - s₁.val) * w i₀ := by
        rw [Nat.sub_mul]
        exact (Nat.modEq_iff_dvd' (Nat.mul_le_mul_right _ hlt.le)).mp hmod_eq
      have hdvd_diff : p ∣ s₂.val - s₁.val := hcop.symm.dvd_of_dvd_mul_right hdvd_sub
      have hle_p : p ≤ s₂.val - s₁.val := Nat.le_of_dvd (by omega) hdvd_diff
      omega
    · have hdvd_sub : p ∣ (s₁.val - s₂.val) * w i₀ := by
        rw [Nat.sub_mul]
        exact (Nat.modEq_iff_dvd' (Nat.mul_le_mul_right _ hgt.le)).mp hmod_eq.symm
      have hdvd_diff : p ∣ s₁.val - s₂.val := hcop.symm.dvd_of_dvd_mul_right hdvd_sub
      have hle_p : p ≤ s₁.val - s₂.val := Nat.le_of_dvd (by omega) hdvd_diff
      omega
  have h_surj : Function.Surjective mulMod :=
    (Fintype.bijective_iff_injective_and_card mulMod).mpr ⟨h_inj, rfl⟩ |>.2
  obtain ⟨s, hs_eq⟩ := h_surj ⟨r, hr_lt⟩
  have hs_mod : (s.val * w i₀) % p = r := congr_arg Fin.val hs_eq
  let q_s : ℕ := (s.val * w i₀) / p
  have hs_div : p * q_s + r = s.val * w i₀ := by rw [← hs_mod]; exact Nat.div_add_mod _ _
  refine ⟨(t' + (s.val : ℝ)) / (p : ℝ), by positivity, fun i => ?_⟩
  rcases eq_or_ne i i₀ with hi_eq | hne
  · rw [hi_eq]
    have h_expand : (t' + (s.val : ℝ)) / (p : ℝ) * (w i₀ : ℝ) =
        ((⌊α⌋ + (q_s : ℤ) + z : ℤ) : ℝ) - (z : ℝ) + (fr + (r : ℝ) / (p : ℝ)) := by
      have hs_cast : (s.val : ℝ) * (w i₀ : ℝ) = (p : ℝ) * (q_s : ℝ) + (r : ℝ) := by
        exact_mod_cast hs_div.symm
      have hα_split : (⌊α⌋ : ℝ) + fr = α := Int.floor_add_fract α
      calc (t' + (s.val : ℝ)) / (p : ℝ) * (w i₀ : ℝ)
          = α + ((s.val : ℝ) * (w i₀ : ℝ)) / (p : ℝ) := by dsimp [α]; ring
        _ = ((⌊α⌋ : ℝ) + fr) + ((p : ℝ) * (q_s : ℝ) + (r : ℝ)) / (p : ℝ) := by rw [hα_split, hs_cast]
        _ = (⌊α⌋ : ℝ) + (q_s : ℝ) + (fr + (r : ℝ) / (p : ℝ)) := by field_simp [ne_of_gt hp_pos_r]; ring
        _ = ((⌊α⌋ + (q_s : ℤ) + z : ℤ) : ℝ) - (z : ℝ) + (fr + (r : ℝ) / (p : ℝ)) := by push_cast; ring
    have hdist_14 : dist (((t' + (s.val : ℝ)) / (p : ℝ) * (w i₀ : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 4 := by
      refine unitAddCircle_dist_ge_of_Icc _ (1 / 4) (⌊α⌋ + (q_s : ℤ) + z) ?_ ?_
      · rw [h_expand]; linarith
      · rw [h_expand]; linarith
    have hm4 : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 4 ≤ m + 1))
    exact le_trans hm4 hdist_14
  · have hi_U : i ∈ (U : Set (Fin m)) :=
      Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i⟩)
    have hrange : Set.range emb = (U : Set (Fin m)) := Finset.range_orderEmbOfFin U hU_card
    obtain ⟨l, hl⟩ : ∃ l : Fin (m - 1), emb l = i := by rwa [← hrange] at hi_U
    have hw_eq : (w i : ℝ) = (p : ℝ) * (u l : ℝ) := by
      rw [← hl]; exact_mod_cast (hu_mul l).symm
    have h_mul : (t' + (s.val : ℝ)) / (p : ℝ) * (w i : ℝ) =
        t' * (u l : ℝ) + (((s.val * u l : ℕ) : ℤ) : ℝ) := by
      rw [hw_eq]; push_cast; field_simp [ne_of_gt hp_pos_r]
    have h_coe : (((t' + (s.val : ℝ)) / (p : ℝ) * (w i : ℝ) : ℝ) : UnitAddCircle) =
        ((t' * (u l : ℝ) : ℝ) : UnitAddCircle) := by
      rw [h_mul, QuotientAddGroup.mk_add, unitAddCircle_int_cast_eq_zero, add_zero]
    rw [h_coe]
    have hstep := ht'_lonely l
    have hm_sub : m - 1 + 1 = m := by omega
    rw [hm_sub] at hstep
    have hfrac : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 / (m : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (Nat.le_succ m))
    exact le_trans hfrac hstep

/- ### Module 2: Small-Divisor Sieve, Prime Filtering & Unconditional 5-Runner Theorem (k = 4) -/

private lemma unitAddCircle_dist_ge_of_mod_Icc {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (lam w : ℕ) (hlo : N ≤ p * ((lam * w) % N)) (hhi : p * ((lam * w) % N) ≤ (p - 1) * N) :
    dist (((((lam : ℝ) / (N : ℝ)) * (w : ℝ) : ℝ)) : UnitAddCircle) 0 ≥ 1 / (p : ℝ) := by
  let q_nat : ℕ := (lam * w) / N
  let r_nat : ℕ := (lam * w) % N
  have hdiv : N * q_nat + r_nat = lam * w := Nat.div_add_mod (lam * w) N
  have hdiv_real : (N : ℝ) * (q_nat : ℝ) + (r_nat : ℝ) = (lam : ℝ) * (w : ℝ) := by
    exact_mod_cast hdiv
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  have hx_eq : ((lam : ℝ) / (N : ℝ)) * (w : ℝ) = ((q_nat : ℤ) : ℝ) + (r_nat : ℝ) / (N : ℝ) := by
    push_cast
    field_simp [ne_of_gt hN_pos]
    linarith
  have hlo_real : (N : ℝ) ≤ (p : ℝ) * (r_nat : ℝ) := by exact_mod_cast hlo
  have hhi_real : (p : ℝ) * (r_nat : ℝ) ≤ ((p - 1 : ℕ) : ℝ) * (N : ℝ) := by exact_mod_cast hhi
  have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hp1] at hhi_real
  refine unitAddCircle_dist_ge_of_Icc _ (1 / (p : ℝ)) (q_nat : ℤ) ?_ ?_
  · rw [hx_eq]
    have h1 : 1 / (p : ℝ) ≤ (r_nat : ℝ) / (N : ℝ) := by
      rw [div_le_div_iff₀ hp_pos hN_pos]
      linarith
    linarith
  · rw [hx_eq]
    have h2 : (r_nat : ℝ) / (N : ℝ) ≤ 1 - 1 / (p : ℝ) := by
      have hsub : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by
        field_simp [ne_of_gt hp_pos]
      rw [hsub, div_le_div_iff₀ hN_pos hp_pos]
      linarith
    linarith

private lemma lrc_small_divisor_sieve {k j : ℕ} (hj2 : 2 ≤ j) (hjk : j ≤ k + 1)
    (w : Fin k → ℕ) (hnot_dvd : ∀ i : Fin k, ¬ (j ∣ w i)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  refine ⟨1 / (j : ℝ), by positivity, fun i => ?_⟩
  have hmod_ne : (1 * w i) % j ≠ 0 := by
    rw [one_mul]
    intro h0
    exact hnot_dvd i (Nat.dvd_of_mod_eq_zero h0)
  have hmod_ge : 1 ≤ (1 * w i) % j := Nat.one_le_iff_ne_zero.mpr hmod_ne
  have hmod_lt : (1 * w i) % j < j := Nat.mod_lt _ (by omega)
  have hmod_le : (1 * w i) % j ≤ j - 1 := by omega
  have hdist_j : dist ((((1 : ℝ) / (j : ℝ)) * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / (j : ℝ) := by
    simpa [Nat.cast_one] using
      unitAddCircle_dist_ge_of_mod_Icc (N := j) (p := j) (by omega) hj2 1 (w i)
        (by nlinarith) (by nlinarith)
  have hj_pos : (0 : ℝ) < (j : ℝ) := by positivity
  have hjk_real : (j : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hjk
  exact le_trans (one_div_le_one_div_of_le hj_pos hjk_real) hdist_j

private lemma exists_pow_mul_not_dvd {p : ℕ} (hp : 2 ≤ p) :
    ∀ n : ℕ, 0 < n → ∃ e u : ℕ, 0 < u ∧ ¬ (p ∣ u) ∧ n = p ^ e * u := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hdvd : p ∣ n
    · obtain ⟨m, hm⟩ := hdvd
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp at hm; omega
        · exact hpos
      have hm_lt : m < n := by nlinarith
      obtain ⟨e, u, hu_pos, hnot, hmu⟩ := ih m hm_lt hm_pos
      refine ⟨e + 1, u, hu_pos, hnot, ?_⟩
      rw [hm, hmu, pow_succ]
      ring
    · exact ⟨0, n, hn, hdvd, by simp⟩

private lemma div_pow_mod_pow_succ {p m : ℕ} (hp : 2 ≤ p) (a s : ℕ) (hs : s < p ^ m) :
    ((a * p ^ m + s) % p ^ (m + 1)) / p ^ m = a % p := by
  have hpm_pos : 0 < p ^ m := pow_pos (by omega) m
  have ha_eq : a = p * (a / p) + a % p := (Nat.div_add_mod a p).symm
  have hlt : (a % p) * p ^ m + s < p ^ (m + 1) := by
    have hap : a % p ≤ p - 1 := by
      have := Nat.mod_lt a (by omega : 0 < p)
      omega
    calc
      (a % p) * p ^ m + s ≤ (p - 1) * p ^ m + s :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ hap) s
      _ < (p - 1) * p ^ m + p ^ m := Nat.add_lt_add_left hs _
      _ = p ^ (m + 1) := by
        rw [pow_succ']
        cases p with
        | zero => omega
        | succ p' => simp [Nat.succ_mul]
  have hrew : a * p ^ m + s = ((a % p) * p ^ m + s) + p ^ (m + 1) * (a / p) := by
    conv_lhs => rw [ha_eq]
    rw [pow_succ']
    ring
  rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpm_pos, Nat.div_eq_of_lt hs, zero_add]

private lemma add_mul_mod_inj {p : ℕ} (hp : Nat.Prime p) {q₀ b : ℕ} (hb : ¬ (p ∣ b)) :
    Function.Injective (fun x : Fin p => (q₀ + x.val * b) % p) := by
  intro x₁ x₂ heq
  by_contra hne
  have hval_ne : x₁.val ≠ x₂.val := fun hv => hne (Fin.ext hv)
  have hcop : Nat.Coprime p b := hp.coprime_iff_not_dvd.mpr hb
  rcases lt_or_gt_of_ne hval_ne with hlt | hgt
  · have hle : q₀ + x₁.val * b ≤ q₀ + x₂.val * b :=
      Nat.add_le_add_left (Nat.mul_le_mul_right b hlt.le) q₀
    have hdvd1 : p ∣ (q₀ + x₂.val * b) - (q₀ + x₁.val * b) :=
      (Nat.modEq_iff_dvd' hle).mp heq
    have hsub : (q₀ + x₂.val * b) - (q₀ + x₁.val * b) = (x₂.val - x₁.val) * b := by
      rw [Nat.add_sub_add_left, ← Nat.sub_mul]
    rw [hsub] at hdvd1
    have hdvd_diff : p ∣ x₂.val - x₁.val := hcop.dvd_of_dvd_mul_right hdvd1
    have := Nat.le_of_dvd (by omega) hdvd_diff
    omega
  · have hle : q₀ + x₂.val * b ≤ q₀ + x₁.val * b :=
      Nat.add_le_add_left (Nat.mul_le_mul_right b hgt.le) q₀
    have hdvd1 : p ∣ (q₀ + x₁.val * b) - (q₀ + x₂.val * b) :=
      (Nat.modEq_iff_dvd' hle).mp heq.symm
    have hsub : (q₀ + x₁.val * b) - (q₀ + x₂.val * b) = (x₁.val - x₂.val) * b := by
      rw [Nat.add_sub_add_left, ← Nat.sub_mul]
    rw [hsub] at hdvd1
    have hdvd_diff : p ∣ x₁.val - x₂.val := hcop.dvd_of_dvd_mul_right hdvd1
    have := Nat.le_of_dvd (by omega) hdvd_diff
    omega

private lemma card_filter_eq_le_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) {f : α → β} (hf : Function.Injective f) (y : β) :
    (s.filter (fun x => f x = y)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  exact hf (ha.2.trans hb.2.symm)

private theorem prime_filtering_step {k p m : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hm : 1 ≤ m)
    (e u : Fin k → ℕ) (hu_not : ∀ i, ¬ (p ∣ u i))
    (hlevel : ∀ j < m, (Finset.univ.filter (fun i : Fin k => e i = j)).card ≤ (p - 1) / 2) :
    ∀ t ≤ m, ∃ lam : ℕ, ¬ (p ∣ lam) ∧
      ∀ i : Fin k, m - t ≤ e i → e i < m →
        1 ≤ ((lam * (p ^ (e i) * u i)) % p ^ (m + 1)) / p ^ m ∧
        ((lam * (p ^ (e i) * u i)) % p ^ (m + 1)) / p ^ m ≤ p - 2 := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨1, ?_, fun i hge hlt => by omega⟩
    intro hdvd
    have := Nat.le_of_dvd zero_lt_one hdvd
    omega
  | succ t ih =>
    intro ht_le
    obtain ⟨lam₀, hlam₀, hprev⟩ := ih (by omega)
    let j : ℕ := m - (t + 1)
    have hj_lt : j < m := by omega
    let Sj : Finset (Fin k) := Finset.univ.filter (fun i => e i = j)
    let f_digit : Fin k → Fin p → ℕ :=
      fun i x => (((lam₀ * (1 + x.val * p ^ (m - j))) * (p ^ (e i) * u i)) % p ^ (m + 1)) / p ^ m
    have hdigit_formula : ∀ i ∈ Sj, ∀ x : Fin p,
        f_digit i x = ((((lam₀ * (p ^ j * u i)) % p ^ (m + 1)) / p ^ m) +
          x.val * (lam₀ * u i)) % p := by
      intro i hi x
      have hei : e i = j := (Finset.mem_filter.mp hi).2
      dsimp [f_digit]
      rw [hei]
      let q₀ : ℕ := ((lam₀ * (p ^ j * u i)) % p ^ (m + 1)) / p ^ m
      let s₀ : ℕ := ((lam₀ * (p ^ j * u i)) % p ^ (m + 1)) % p ^ m
      have hs₀_lt : s₀ < p ^ m := Nat.mod_lt _ (pow_pos (by omega) m)
      have hrem_decomp : (lam₀ * (p ^ j * u i)) % p ^ (m + 1) = q₀ * p ^ m + s₀ := by
        dsimp only [q₀, s₀]
        rw [mul_comm _ (p ^ m), Nat.div_add_mod]
      have hpow_add : p ^ (m - j) * p ^ j = p ^ m := by
        rw [← pow_add, Nat.sub_add_cancel (le_of_lt hj_lt)]
      have hexpand : (lam₀ * (1 + x.val * p ^ (m - j))) * (p ^ j * u i) =
          lam₀ * (p ^ j * u i) + (x.val * (lam₀ * u i)) * p ^ m := by
        calc
          (lam₀ * (1 + x.val * p ^ (m - j))) * (p ^ j * u i)
            = lam₀ * (p ^ j * u i) + (x.val * (lam₀ * u i)) * (p ^ (m - j) * p ^ j) := by ring
          _ = lam₀ * (p ^ j * u i) + (x.val * (lam₀ * u i)) * p ^ m := by rw [hpow_add]
      have hmod_N : ((lam₀ * (1 + x.val * p ^ (m - j))) * (p ^ j * u i)) % p ^ (m + 1) =
          ((q₀ + x.val * (lam₀ * u i)) * p ^ m + s₀) % p ^ (m + 1) := by
        rw [hexpand]
        conv_lhs => rw [← Nat.div_add_mod (lam₀ * (p ^ j * u i)) (p ^ (m + 1)), hrem_decomp]
        have hring : p ^ (m + 1) * (lam₀ * (p ^ j * u i) / p ^ (m + 1)) + (q₀ * p ^ m + s₀) +
            x.val * (lam₀ * u i) * p ^ m =
            ((q₀ + x.val * (lam₀ * u i)) * p ^ m + s₀) +
            p ^ (m + 1) * (lam₀ * (p ^ j * u i) / p ^ (m + 1)) := by ring
        rw [hring, Nat.add_mul_mod_self_left]
      rw [hmod_N]
      exact div_pow_mod_pow_succ (by omega) (q₀ + x.val * (lam₀ * u i)) s₀ hs₀_lt
    let badFor : Fin k → Finset (Fin p) :=
      fun i => Finset.univ.filter (fun x : Fin p => f_digit i x = 0 ∨ f_digit i x = p - 1)
    have hbad_card : ∀ i ∈ Sj, (badFor i).card ≤ 2 := by
      intro i hi
      have hb_not : ¬ (p ∣ lam₀ * u i) := by
        intro hdvd
        rcases hp.dvd_mul.mp hdvd with h1 | h2
        · exact hlam₀ h1
        · exact hu_not i h2
      let g : Fin p → ℕ :=
        fun x => ((((lam₀ * (p ^ j * u i)) % p ^ (m + 1)) / p ^ m) + x.val * (lam₀ * u i)) % p
      have hg_inj : Function.Injective g := add_mul_mod_inj hp hb_not
      have hsub : badFor i ⊆
          (Finset.univ.filter (fun x => g x = 0)) ∪ (Finset.univ.filter (fun x => g x = p - 1)) := by
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [hdigit_formula i hi x] at hx
        rcases hx.2 with h0 | hp1
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h0⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hp1⟩)
      calc
        (badFor i).card ≤ ((Finset.univ.filter (fun x => g x = 0)) ∪
            (Finset.univ.filter (fun x => g x = p - 1))).card := Finset.card_le_card hsub
        _ ≤ (Finset.univ.filter (fun x => g x = 0)).card +
            (Finset.univ.filter (fun x => g x = p - 1)).card := Finset.card_union_le _ _
        _ ≤ 1 + 1 := Nat.add_le_add (card_filter_eq_le_one _ hg_inj 0)
            (card_filter_eq_le_one _ hg_inj (p - 1))
        _ = 2 := rfl
    let allBad : Finset (Fin p) := Sj.biUnion badFor
    have hallBad_lt : allBad.card < p := by
      calc
        allBad.card ≤ ∑ i ∈ Sj, (badFor i).card := Finset.card_biUnion_le
        _ ≤ ∑ _ ∈ Sj, 2 := Finset.sum_le_sum hbad_card
        _ = 2 * Sj.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 2 * ((p - 1) / 2) := Nat.mul_le_mul_left 2 (hlevel j hj_lt)
        _ ≤ p - 1 := Nat.mul_div_le (p - 1) 2
        _ < p := by omega
    have hexists_good : (Finset.univ \ allBad).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have hsub : (Finset.univ : Finset (Fin p)) ⊆ allBad := Finset.sdiff_eq_empty_iff_subset.mp hemp
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_fin] at hcard
      omega
    obtain ⟨x₀, hx₀⟩ := hexists_good
    have hx₀_not_bad : x₀ ∉ allBad := (Finset.mem_sdiff.mp hx₀).2
    let lam : ℕ := lam₀ * (1 + x₀.val * p ^ (m - j))
    have hlam_not : ¬ (p ∣ lam) := by
      intro hdvd
      rcases hp.dvd_mul.mp hdvd with h1 | h2
      · exact hlam₀ h1
      · have hdvd_pow : p ∣ x₀.val * p ^ (m - j) := by
          refine dvd_mul_of_dvd_right ?_ x₀.val
          exact dvd_pow_self p (by omega)
        have hdvd_one : p ∣ 1 := (Nat.dvd_add_left hdvd_pow).mp h2
        have := Nat.le_of_dvd zero_lt_one hdvd_one
        omega
    refine ⟨lam, hlam_not, fun i hge hlt => ?_⟩
    rcases eq_or_lt_of_le hge with hei_eq | hei_gt
    · have hi_mem : i ∈ Sj := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hei_eq.symm⟩
      have hx_not_i : x₀ ∉ badFor i := fun h => hx₀_not_bad (Finset.mem_biUnion.mpr ⟨i, hi_mem, h⟩)
      have hnot_or : ¬ (f_digit i x₀ = 0 ∨ f_digit i x₀ = p - 1) := by
        intro hor
        exact hx_not_i (Finset.mem_filter.mpr ⟨Finset.mem_univ x₀, hor⟩)
      have hlt_p : f_digit i x₀ < p := by
        dsimp [f_digit]
        have hlt_N := Nat.mod_lt ((lam₀ * (1 + x₀.val * p ^ (m - j))) * (p ^ (e i) * u i))
          (pow_pos (by omega : 0 < p) (m + 1))
        rw [pow_succ] at hlt_N
        exact Nat.div_lt_of_lt_mul hlt_N
      change 1 ≤ f_digit i x₀ ∧ f_digit i x₀ ≤ p - 2
      omega
    · have hge_prev : m - t ≤ e i := by omega
      have hmod_same : (lam * (p ^ (e i) * u i)) % p ^ (m + 1) =
          (lam₀ * (p ^ (e i) * u i)) % p ^ (m + 1) := by
        dsimp [lam]
        have he_split : m - j + e i = (m + 1) + (e i - (j + 1)) := by omega
        have hexp : (lam₀ * (1 + x₀.val * p ^ (m - j))) * (p ^ (e i) * u i) =
            lam₀ * (p ^ (e i) * u i) +
            p ^ (m + 1) * (lam₀ * x₀.val * u i * p ^ (e i - (j + 1))) := by
          calc
            (lam₀ * (1 + x₀.val * p ^ (m - j))) * (p ^ (e i) * u i)
              = lam₀ * (p ^ (e i) * u i) +
                (lam₀ * x₀.val * u i) * (p ^ (m - j) * p ^ (e i)) := by ring
            _ = lam₀ * (p ^ (e i) * u i) +
                (lam₀ * x₀.val * u i) * p ^ ((m + 1) + (e i - (j + 1))) := by
                  rw [← pow_add, he_split]
            _ = lam₀ * (p ^ (e i) * u i) +
                p ^ (m + 1) * (lam₀ * x₀.val * u i * p ^ (e i - (j + 1))) := by
                  rw [pow_add]; ring
        rw [hexp, Nat.add_mul_mod_self_left]
      rw [hmod_same]
      exact hprev i hge_prev hlt

private theorem prime_filtering_finish {k p m : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (w e u : Fin k → ℕ) (hu_not : ∀ i, ¬ (p ∣ u i))
    (hw_decomp : ∀ i, w i = p ^ (e i) * u i) (he_le : ∀ i, e i ≤ m)
    (lam : ℕ) (hlam_not : ¬ (p ∣ lam))
    (hdigits : ∀ i : Fin k, e i < m →
      1 ≤ ((lam * w i) % p ^ (m + 1)) / p ^ m ∧
      ((lam * w i) % p ^ (m + 1)) / p ^ m ≤ p - 2) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / (p : ℝ) := by
  let N : ℕ := p ^ (m + 1)
  have hN_pos : 0 < N := pow_pos (by omega) (m + 1)
  refine ⟨(lam : ℝ) / (N : ℝ), by positivity, fun i => ?_⟩
  rcases lt_or_eq_of_le (he_le i) with hlt | heq
  · obtain ⟨hq_lo, hq_hi⟩ := hdigits i hlt
    let q_i : ℕ := ((lam * w i) % N) / p ^ m
    let s_i : ℕ := ((lam * w i) % N) % p ^ m
    have hq_lo' : 1 ≤ q_i := hq_lo
    have hq_hi' : q_i ≤ p - 2 := hq_hi
    have hs_lt : s_i < p ^ m := Nat.mod_lt _ (pow_pos (by omega) m)
    have hrem_eq : (lam * w i) % N = p ^ m * q_i + s_i :=
      (Nat.div_add_mod ((lam * w i) % N) (p ^ m)).symm
    have hN_eq : N = p * p ^ m := pow_succ' p m
    have hlo : N ≤ p * ((lam * w i) % N) := by
      rw [hrem_eq, hN_eq]
      have : p ^ m ≤ p ^ m * q_i := Nat.le_mul_of_pos_right _ (by omega)
      nlinarith
    have hhi : p * ((lam * w i) % N) ≤ (p - 1) * N := by
      rw [hrem_eq, hN_eq]
      have h1 : p ^ m * q_i + s_i ≤ p ^ m * (p - 2) + (p ^ m - 1) := by
        have hmul : p ^ m * q_i ≤ p ^ m * (p - 2) := Nat.mul_le_mul_left _ hq_hi'
        omega
      have h2 : p ^ m * (p - 2) + (p ^ m - 1) < p ^ m * (p - 1) := by
        have hpm_pos : 0 < p ^ m := pow_pos (by omega) m
        have hsub : p - 1 = (p - 2) + 1 := by omega
        rw [hsub, Nat.mul_add, Nat.mul_one]
        omega
      have h3 : p ^ m * q_i + s_i ≤ p ^ m * (p - 1) := by omega
      nlinarith
    exact unitAddCircle_dist_ge_of_mod_Icc hN_pos (by omega) lam (w i) hlo hhi
  · have hwi : w i = p ^ m * u i := by rw [hw_decomp i, heq]
    have hprod_not : ¬ (p ∣ lam * u i) := by
      intro hdvd
      rcases hp.dvd_mul.mp hdvd with h1 | h2
      · exact hlam_not h1
      · exact hu_not i h2
    let r_u : ℕ := (lam * u i) % p
    have hru_ge : 1 ≤ r_u := by
      refine Nat.one_le_iff_ne_zero.mpr ?_
      intro h0
      exact hprod_not (Nat.dvd_of_mod_eq_zero h0)
    have hru_lt : r_u < p := Nat.mod_lt _ (by omega)
    have hru_le : r_u ≤ p - 1 := by omega
    have hmod_eq : (lam * w i) % N = r_u * p ^ m := by
      dsimp [N]
      rw [hwi]
      have hrew : lam * (p ^ m * u i) = r_u * p ^ m + p ^ (m + 1) * ((lam * u i) / p) := by
        have hdiv := (Nat.div_add_mod (lam * u i) p).symm
        calc
          lam * (p ^ m * u i) = (lam * u i) * p ^ m := by ring
          _ = (p * ((lam * u i) / p) + r_u) * p ^ m := by rw [← hdiv]
          _ = r_u * p ^ m + p ^ (m + 1) * ((lam * u i) / p) := by rw [pow_succ']; ring
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
      rw [pow_succ']
      exact Nat.mul_lt_mul_of_pos_right hru_lt (pow_pos (by omega) m)
    have hN_eq : N = p * p ^ m := pow_succ' p m
    have hlo : N ≤ p * ((lam * w i) % N) := by
      rw [hmod_eq, hN_eq]
      nlinarith [pow_pos (by omega : 0 < p) m]
    have hhi : p * ((lam * w i) % N) ≤ (p - 1) * N := by
      rw [hmod_eq, hN_eq]
      nlinarith [pow_pos (by omega : 0 < p) m]
    exact unitAddCircle_dist_ge_of_mod_Icc hN_pos (by omega) lam (w i) hlo hhi

private lemma bs5_decidable_compression :
    ∀ (s : Fin 2) (c0 : Fin 4) (q1 : Fin 5) (c1 : Fin 4),
      ∃ (j : Fin 3) (k0 : Fin 5),
        (let r_val := s.val + 1
         let step_k := if s.val = 0 then 1 else 3
         let c_lookup := fun (c : Fin 4) (jv : ℕ) =>
           if jv = 0 then 0
           else if jv = 1 then (if c.val < 2 then 0 else 1)
           else (if c.val = 0 then 0 else if c.val < 3 then 1 else 2)
         let d0_good1 := (c_lookup c0 j.val + k0.val * r_val) % 5
         let d1_good1 := ((j.val + 1) * q1.val + c_lookup c1 j.val + k0.val * r_val) % 5
         let d0_good2 := (c_lookup c0 j.val + (k0.val + step_k) * r_val) % 5
         let d1_good2 := ((j.val + 1) * q1.val + c_lookup c1 j.val + (k0.val + step_k) * r_val) % 5
         1 ≤ d0_good1 ∧ d0_good1 ≤ 3 ∧ 1 ≤ d1_good1 ∧ d1_good1 ≤ 3 ∧
         1 ≤ d0_good2 ∧ d0_good2 ≤ 3 ∧ 1 ≤ d1_good2 ∧ d1_good2 ≤ 3) := by
  decide

private lemma bs5_decidable_same_class :
    ∀ (s : Fin 2) (c0 : Fin 4) (q1 : Fin 5) (c1 : Fin 4) (q2 : Fin 5) (c2 : Fin 4),
      ∃ (j : Fin 3) (k : Fin 5),
        (let r_val := s.val + 1
         let c_lookup := fun (c : Fin 4) (jv : ℕ) =>
           if jv = 0 then 0
           else if jv = 1 then (if c.val < 2 then 0 else 1)
           else (if c.val = 0 then 0 else if c.val < 3 then 1 else 2)
         let v0 := (c_lookup c0 j.val + k.val * r_val) % 5
         let v1 := ((j.val + 1) * q1.val + c_lookup c1 j.val + k.val * r_val) % 5
         let v2 := ((j.val + 1) * q2.val + c_lookup c2 j.val + k.val * r_val) % 5
         1 ≤ v0 ∧ v0 ≤ 3 ∧ 1 ≤ v1 ∧ v1 ≤ 3 ∧ 1 ≤ v2 ∧ v2 ≤ 3) := by
  decide

private lemma carry_code_exists {m : ℕ} (rem : ℕ) (hrem : rem < 5 ^ m) :
    ∃ c : Fin 4,
      (let c_lookup := fun (jv : ℕ) =>
         if jv = 0 then 0
         else if jv = 1 then (if c.val < 2 then 0 else 1)
         else (if c.val = 0 then 0 else if c.val < 3 then 1 else 2)
       (1 * rem) / 5 ^ m = c_lookup 0 ∧
       (2 * rem) / 5 ^ m = c_lookup 1 ∧
       (3 * rem) / 5 ^ m = c_lookup 2) := by
  have h5m_pos : 0 < 5 ^ m := pow_pos (by omega) m
  have h5m_odd : Odd (5 ^ m) := Odd.pow (by decide : Odd 5)
  obtain ⟨h_half, hh_eq⟩ := h5m_odd
  have hc1 : (1 * rem) / 5 ^ m = 0 := by rw [one_mul]; exact Nat.div_eq_of_lt hrem
  let d2 : ℕ := (2 * rem) / 5 ^ m
  let d3 : ℕ := (3 * rem) / 5 ^ m
  have hd2_lt : d2 < 2 := Nat.div_lt_of_lt_mul (by omega)
  have hd3_lt : d3 < 3 := Nat.div_lt_of_lt_mul (by omega)
  rcases Nat.eq_zero_or_pos d2 with hd2_0 | hd2_pos
  · have h2rem_lt : 2 * rem < 5 ^ m := by
      by_contra hge
      have : 1 ≤ d2 := Nat.div_pos (by omega) h5m_pos
      omega
    have hd3_lt2 : d3 < 2 := Nat.div_lt_of_lt_mul (by omega)
    rcases Nat.eq_zero_or_pos d3 with hd3_0 | hd3_pos
    · refine ⟨⟨0, by decide⟩, ?_⟩
      dsimp; exact ⟨hc1, hd2_0, hd3_0⟩
    · have hd3_1 : d3 = 1 := by omega
      refine ⟨⟨1, by decide⟩, ?_⟩
      dsimp; exact ⟨hc1, hd2_0, hd3_1⟩
  · have hd2_1 : d2 = 1 := by omega
    have h2rem_ge : 5 ^ m ≤ 2 * rem := by
      by_contra hlt
      have : d2 = 0 := Nat.div_eq_of_lt (by omega)
      omega
    have h2rem_gt : 5 ^ m + 1 ≤ 2 * rem := by omega
    have hd3_ge1 : 1 ≤ d3 := Nat.div_pos (by omega) h5m_pos
    rcases eq_or_lt_of_le hd3_ge1 with hd3_1 | hd3_gt1
    · refine ⟨⟨2, by decide⟩, ?_⟩
      dsimp; exact ⟨hc1, hd2_1, hd3_1.symm⟩
    · have hd3_2 : d3 = 2 := by omega
      refine ⟨⟨3, by decide⟩, ?_⟩
      dsimp; exact ⟨hc1, hd2_1, hd3_2⟩

private lemma bs5_three_unit_runners {m : ℕ} (hm : 1 ≤ m) (d : Fin 3 → ℕ)
    (hd_not : ∀ a : Fin 3, ¬ (5 ∣ d a)) :
    ∃ lam : ℕ, ¬ (5 ∣ lam) ∧
      ∀ a : Fin 3,
        1 ≤ ((lam * d a) % 5 ^ (m + 1)) / 5 ^ m ∧
        ((lam * d a) % 5 ^ (m + 1)) / 5 ^ m ≤ 3 := by
  have hp5 : Nat.Prime 5 := by decide
  let N : ℕ := 5 ^ (m + 1)
  have hN_eq : N = 5 * 5 ^ m := pow_succ' 5 m
  have h5m_pos : 0 < 5 ^ m := pow_pos (by omega) m
  have hN_pos : 0 < N := pow_pos (by omega) (m + 1)
  let v : Fin 3 → ℕ := fun a =>
    if (d a) % 5 = 1 ∨ (d a) % 5 = 2 then (d a) % N else N - ((d a) % N)
  have hv_mod5 : ∀ a, v a % 5 = 1 ∨ v a % 5 = 2 := by
    intro a
    have hmodN_mod5 : ((d a) % N) % 5 = (d a) % 5 :=
      Nat.mod_mod_of_dvd (d a) ⟨5 ^ m, hN_eq⟩
    have hrem5_ne : (d a) % 5 ≠ 0 := fun h0 => hd_not a (Nat.dvd_of_mod_eq_zero h0)
    have hrem5_lt : (d a) % 5 < 5 := Nat.mod_lt _ (by omega)
    dsimp [v]
    split_ifs with h12
    · rwa [hmodN_mod5]
    · have h34 : (d a) % 5 = 3 ∨ (d a) % 5 = 4 := by omega
      have hmod_lt : (d a) % N < N := Nat.mod_lt _ hN_pos
      have hsub_mod5 : (N - (d a) % N) % 5 = (5 - ((d a) % N) % 5) % 5 := by
        let r := (d a) % N
        have hr_lt5 : r % 5 < 5 := Nat.mod_lt _ (by decide)
        have hdiv_lt : r / 5 < 5 ^ m := by
          have hr_lt_mul : r < 5 * 5 ^ m := by dsimp [r]; rwa [← hN_eq]
          exact Nat.div_lt_of_lt_mul hr_lt_mul
        have hdiv_le : r / 5 + 1 ≤ 5 ^ m := hdiv_lt
        have hrew_z : (((N - r) : ℕ) : ℤ) =
            ((((5 - r % 5) + 5 * (5 ^ m - (r / 5 + 1))) : ℕ) : ℤ) := by
          have hq_z : (5 : ℤ) * ((r / 5 : ℕ) : ℤ) + ((r % 5 : ℕ) : ℤ) = (r : ℤ) := by
            rw [← Nat.cast_ofNat, ← Nat.cast_mul, ← Nat.cast_add, Nat.div_add_mod]
          have hN_z : (N : ℤ) = (5 : ℤ) * ((5 ^ m : ℕ) : ℤ) := by
            rw [hN_eq, Nat.cast_mul, Nat.cast_ofNat]
          have hr_le_N : r ≤ N := hmod_lt.le
          rw [Nat.cast_sub hr_le_N, Nat.cast_add, Nat.cast_sub hr_lt5.le,
            Nat.cast_mul, Nat.cast_sub hdiv_le, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          linarith
        have hrew : N - r = (5 - r % 5) + 5 * (5 ^ m - (r / 5 + 1)) :=
          Int.ofNat.inj hrew_z
        dsimp [r] at hrew
        rw [hrew, Nat.add_mul_mod_self_left]
      rw [hsub_mod5, hmodN_mod5]
      rcases h34 with h3 | h4 <;> [right; left] <;> omega
  have hv_to_d : ∀ (lam : ℕ) (a : Fin 3), ¬ (5 ∣ lam) →
      (1 ≤ ((lam * v a) % N) / 5 ^ m ∧ ((lam * v a) % N) / 5 ^ m ≤ 3) →
      (1 ≤ ((lam * d a) % N) / 5 ^ m ∧ ((lam * d a) % N) / 5 ^ m ≤ 3) := by
    intro lam a hlam ⟨hlo, hhi⟩
    dsimp [v] at hlo hhi
    split_ifs at hlo hhi with h12
    · rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod] at hlo hhi
      exact ⟨hlo, hhi⟩
    · have h5m_not : ¬ (5 ^ m ∣ lam * d a) := by
        intro hdvd
        have h5_dvd_5m : 5 ∣ 5 ^ m := dvd_pow_self 5 (by omega)
        rcases hp5.dvd_mul.mp (dvd_trans h5_dvd_5m hdvd) with h1 | h2
        · exact hlam h1
        · exact hd_not a h2
      have hrem_pos : 0 < ((lam * d a) % N) % 5 ^ m := by
        refine Nat.pos_of_ne_zero ?_
        intro h0
        have hdvd1 : 5 ^ m ∣ (lam * d a) % N := Nat.dvd_of_mod_eq_zero h0
        have hdvdN : 5 ^ m ∣ N := ⟨5, by rw [hN_eq]; ring⟩
        have hdvd_tot : 5 ^ m ∣ lam * d a := by
          have h := (Nat.div_add_mod (lam * d a) N).symm
          rw [h]
          exact dvd_add (dvd_mul_of_dvd_left hdvdN _) hdvd1
        exact h5m_not hdvd_tot
      have hmod_lt : (d a) % N < N := Nat.mod_lt _ hN_pos
      have hlam_sub : (lam * (N - (d a) % N)) % N = N - (lam * d a) % N := by
        let r : ℕ := (d a) % N
        let rem : ℕ := (lam * r) % N
        let quot : ℕ := (lam * r) / N
        have hrem_eq : rem = (lam * d a) % N := by
          dsimp [rem, r]
          rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
        have hrem_pos' : 0 < rem := by
          rw [hrem_eq]
          exact Nat.pos_of_ne_zero (fun h0 => hrem_pos.ne' (by rw [h0, Nat.zero_mod]))
        have hrem_lt : rem < N := Nat.mod_lt _ hN_pos
        have hlam_pos : 0 < lam := by
          rcases Nat.eq_zero_or_pos lam with rfl | hpos
          · simp [rem] at hrem_pos'
          · exact hpos
        have hquot_lt : quot < lam := by
          have hdiv : N * quot + rem = lam * r := Nat.div_add_mod (lam * r) N
          have h1 : N * quot < lam * r := by omega
          have h2 : lam * r < N * lam := by
            rw [mul_comm N lam]
            exact Nat.mul_lt_mul_of_pos_left hmod_lt hlam_pos
          exact Nat.lt_of_mul_lt_mul_left (lt_trans h1 h2)
        have hquot_le : quot + 1 ≤ lam := hquot_lt
        have hrew_z : (((lam * (N - r)) : ℕ) : ℤ) =
            ((((N - rem) + N * (lam - (quot + 1))) : ℕ) : ℤ) := by
          have hdiv_z : (N : ℤ) * (quot : ℤ) + (rem : ℤ) = (lam : ℤ) * (r : ℤ) := by
            exact_mod_cast Nat.div_add_mod (lam * r) N
          rw [Nat.cast_mul, Nat.cast_sub hmod_lt.le, Nat.cast_add, Nat.cast_sub hrem_lt.le,
            Nat.cast_mul, Nat.cast_sub hquot_le, Nat.cast_add, Nat.cast_one]
          linarith
        have hrew : lam * (N - r) = (N - rem) + N * (lam - (quot + 1)) :=
          Int.ofNat.inj hrew_z
        dsimp [r] at hrew
        rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega), hrem_eq]
      rw [hlam_sub] at hlo hhi
      let q_d : ℕ := ((lam * d a) % N) / 5 ^ m
      let s_d : ℕ := ((lam * d a) % N) % 5 ^ m
      have hs_lt : s_d < 5 ^ m := Nat.mod_lt _ h5m_pos
      have hdecomp : (lam * d a) % N = 5 ^ m * q_d + s_d :=
        (Nat.div_add_mod ((lam * d a) % N) (5 ^ m)).symm
      have hqd_lt : q_d < 5 := by
        have hltN : (lam * d a) % N < 5 ^ m * 5 := by
          rw [← pow_succ]
          exact Nat.mod_lt _ hN_pos
        exact Nat.div_lt_of_lt_mul hltN
      have hsub_div : (N - (lam * d a) % N) / 5 ^ m = 4 - q_d := by
        have hltN : (lam * d a) % N < N := Nat.mod_lt _ hN_pos
        have hqd_le : q_d ≤ 4 := by omega
        have hrew_z : (((N - (lam * d a) % N) : ℕ) : ℤ) =
            ((((5 ^ m - s_d) + (4 - q_d) * 5 ^ m) : ℕ) : ℤ) := by
          have hdec_z : (((lam * d a) % N : ℕ) : ℤ) = (5 ^ m : ℤ) * (q_d : ℤ) + (s_d : ℤ) := by
            exact_mod_cast hdecomp
          have hN_z : (N : ℤ) = 5 * (5 ^ m : ℤ) := by exact_mod_cast hN_eq
          rw [Nat.cast_sub hltN.le, Nat.cast_add, Nat.cast_sub hs_lt.le,
            Nat.cast_mul, Nat.cast_sub hqd_le]
          push_cast
          linarith
        have hrew : N - (lam * d a) % N = (5 ^ m - s_d) + (4 - q_d) * 5 ^ m :=
          Int.ofNat.inj hrew_z
        have h5s_lt : 5 ^ m - s_d < 5 ^ m := by omega
        rw [hrew, Nat.add_mul_div_right _ _ h5m_pos, Nat.div_eq_of_lt h5s_lt, zero_add]
      rw [hsub_div] at hlo hhi
      omega
  have hs12_0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
  have hs12_1 : Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide
  have hs02_0 : Equiv.swap (0 : Fin 3) 2 0 = 2 := by decide
  have hs02_1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := by decide
  have hexists_perm : ∃ perm : Equiv.Perm (Fin 3), v (perm 0) % 5 = v (perm 1) % 5 := by
    rcases hv_mod5 0 with h0 | h0 <;> rcases hv_mod5 1 with h1 | h1 <;> rcases hv_mod5 2 with h2 | h2
    · exact ⟨Equiv.refl _, by simp [h0, h1]⟩
    · exact ⟨Equiv.refl _, by simp [h0, h1]⟩
    · exact ⟨Equiv.swap 1 2, by rw [hs12_0, hs12_1, h0, h2]⟩
    · exact ⟨Equiv.swap 0 2, by rw [hs02_0, hs02_1, h2, h1]⟩
    · exact ⟨Equiv.swap 0 2, by rw [hs02_0, hs02_1, h2, h1]⟩
    · exact ⟨Equiv.swap 1 2, by rw [hs12_0, hs12_1, h0, h2]⟩
    · exact ⟨Equiv.refl _, by simp [h0, h1]⟩
    · exact ⟨Equiv.refl _, by simp [h0, h1]⟩
  obtain ⟨perm, hperm01⟩ := hexists_perm
  let u : Fin 3 → ℕ := fun a => v (perm a)
  have hu0_not : ¬ (5 ∣ u 0) := by
    intro hdvd
    have h0 : u 0 % 5 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    dsimp only [u] at h0
    rcases hv_mod5 (perm 0) with h | h <;> omega
  have hshift_inj := add_mul_mod_inj hp5 hu0_not (q₀ := (u 0) / 5 ^ m)
  have hshift_surj : Function.Surjective
      (fun x : Fin 5 => ⟨((u 0) / 5 ^ m + x.val * u 0) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5 → Fin 5) := by
    refine Finite.injective_iff_surjective.mp ?_
    intro x₁ x₂ h
    exact hshift_inj (congr_arg Fin.val h)
  obtain ⟨x_init, hx_init⟩ := hshift_surj ⟨0, by decide⟩
  let mu₀ : ℕ := 1 + x_init.val * 5 ^ m
  have hmu₀_not : ¬ (5 ∣ mu₀) := by
    intro hdvd
    have hdvd_pow : 5 ∣ x_init.val * 5 ^ m := dvd_mul_of_dvd_right (dvd_pow_self 5 (by omega)) _
    have hdvd1 : 5 ∣ 1 := (Nat.dvd_add_left hdvd_pow).mp hdvd
    have := Nat.le_of_dvd zero_lt_one hdvd1
    omega
  let w' : Fin 3 → ℕ := fun a => (mu₀ * u a) % N
  have hw'_mod5 : ∀ a, w' a % 5 = u a % 5 := by
    intro a
    dsimp [w', mu₀]
    have hdvd5 : 5 ∣ N := ⟨5 ^ m, hN_eq⟩
    rw [Nat.mod_mod_of_dvd _ hdvd5]
    have hrew : (1 + x_init.val * 5 ^ m) * u a =
        u a + 5 * (x_init.val * 5 ^ (m - 1) * u a) := by
      have hm1 : 5 ^ m = 5 * 5 ^ (m - 1) := by
        conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
      rw [hm1]; ring
    rw [hrew, Nat.add_mul_mod_self_left]
  have hw'0_div : w' 0 / 5 ^ m = 0 := by
    dsimp [w', mu₀, N]
    let q_u0 : ℕ := u 0 / 5 ^ m
    let s_u0 : ℕ := u 0 % 5 ^ m
    have hs_lt : s_u0 < 5 ^ m := Nat.mod_lt _ h5m_pos
    have hu0_eq : u 0 = q_u0 * 5 ^ m + s_u0 := by
      dsimp only [q_u0, s_u0]
      rw [mul_comm _ (5 ^ m), Nat.div_add_mod]
    have hrew : (1 + x_init.val * 5 ^ m) * u 0 =
        ((q_u0 + x_init.val * u 0) * 5 ^ m + s_u0) := by
      calc
        (1 + x_init.val * 5 ^ m) * u 0 = u 0 + (x_init.val * u 0) * 5 ^ m := by ring
        _ = (q_u0 * 5 ^ m + s_u0) + (x_init.val * u 0) * 5 ^ m := by rw [hu0_eq]
        _ = (q_u0 + x_init.val * u 0) * 5 ^ m + s_u0 := by ring
    rw [hrew, div_pow_mod_pow_succ (by decide) _ _ hs_lt]
    exact congr_arg Fin.val hx_init
  let q_fn : Fin 3 → Fin 5 := fun a =>
    ⟨w' a / 5 ^ m, by
      have hlt : w' a < 5 ^ m * 5 := by
        rw [← pow_succ]
        exact Nat.mod_lt _ hN_pos
      exact Nat.div_lt_of_lt_mul hlt⟩
  let rem_fn : Fin 3 → ℕ := fun a => w' a % 5 ^ m
  obtain ⟨c0, hc0⟩ := carry_code_exists (rem_fn 0) (Nat.mod_lt _ h5m_pos)
  obtain ⟨c1, hc1⟩ := carry_code_exists (rem_fn 1) (Nat.mod_lt _ h5m_pos)
  obtain ⟨c2, hc2⟩ := carry_code_exists (rem_fn 2) (Nat.mod_lt _ h5m_pos)
  let s_class : Fin 2 := if w' 0 % 5 = 1 then ⟨0, by decide⟩ else ⟨1, by decide⟩
  have hs_val : s_class.val + 1 = w' 0 % 5 := by
    dsimp [s_class]
    have h012 : w' 0 % 5 = 1 ∨ w' 0 % 5 = 2 := by rw [hw'_mod5 0]; exact hv_mod5 (perm 0)
    rcases h012 with h1 | h2
    · simp [h1]
    · simp [h2]
  have hw'1_mod5 : w' 1 % 5 = s_class.val + 1 := by
    rw [hs_val, hw'_mod5 1, hw'_mod5 0]
    exact hperm01.symm
  let c_lookup := fun (c : Fin 4) (jv : ℕ) =>
    if jv = 0 then 0
    else if jv = 1 then (if c.val < 2 then 0 else 1)
    else (if c.val = 0 then 0 else if c.val < 3 then 1 else 2)
  have h_eval_digit : ∀ (a : Fin 3) (c_a : Fin 4),
      ((1 * rem_fn a) / 5 ^ m = c_lookup c_a 0 ∧
       (2 * rem_fn a) / 5 ^ m = c_lookup c_a 1 ∧
       (3 * rem_fn a) / 5 ^ m = c_lookup c_a 2) →
      ∀ (j : Fin 3) (k : ℕ),
        ((((j.val + 1) + k * 5 ^ m) * w' a) % N) / 5 ^ m =
          ((j.val + 1) * (q_fn a).val + c_lookup c_a j.val + k * (w' a % 5)) % 5 := by
    intro a c_a ⟨hc_0, hc_1, hc_2⟩ j k
    have hj012 : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
    have hc_j : ((j.val + 1) * rem_fn a) / 5 ^ m = c_lookup c_a j.val := by
      rcases hj012 with rfl | rfl | rfl
      · exact hc_0
      · exact hc_1
      · exact hc_2
    let s_rem : ℕ := ((j.val + 1) * rem_fn a) % 5 ^ m
    have hs_rem_lt : s_rem < 5 ^ m := Nat.mod_lt _ h5m_pos
    have hj_rem_eq : (j.val + 1) * rem_fn a = c_lookup c_a j.val * 5 ^ m + s_rem := by
      dsimp only [s_rem]
      rw [← hc_j, mul_comm _ (5 ^ m), Nat.div_add_mod]
    have hw'_eq : w' a = (q_fn a).val * 5 ^ m + rem_fn a := by
      dsimp only [q_fn, rem_fn]
      rw [mul_comm _ (5 ^ m), Nat.div_add_mod]
    have hrem_mod5 : rem_fn a % 5 = w' a % 5 := by
      dsimp [rem_fn]
      exact Nat.mod_mod_of_dvd (w' a) (dvd_pow_self 5 (by omega))
    have hrem_div5 : rem_fn a = 5 * (rem_fn a / 5) + (w' a % 5) := by
      rw [← hrem_mod5]
      exact (Nat.div_add_mod (rem_fn a) 5).symm
    have h2m : 5 ^ m * 5 ^ m = N * 5 ^ (m - 1) := by
      dsimp [N]
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have hexp : (((j.val + 1) + k * 5 ^ m) * w' a) % N =
        (((j.val + 1) * (q_fn a).val + c_lookup c_a j.val + k * (w' a % 5)) * 5 ^ m + s_rem) % N := by
      conv_lhs => rw [hw'_eq]
      have h1 : ((j.val + 1) + k * 5 ^ m) * ((q_fn a).val * 5 ^ m + rem_fn a) =
          (j.val + 1) * (q_fn a).val * 5 ^ m + (j.val + 1) * rem_fn a +
          k * (q_fn a).val * (5 ^ m * 5 ^ m) + k * rem_fn a * 5 ^ m := by ring
      have h2 : k * rem_fn a * 5 ^ m = k * (w' a % 5) * 5 ^ m + N * (k * (rem_fn a / 5)) := by
        conv_lhs => rw [hrem_div5]
        rw [hN_eq]
        ring
      rw [h1, hj_rem_eq, h2m, h2]
      have h3 : (j.val + 1) * (q_fn a).val * 5 ^ m + (c_lookup c_a j.val * 5 ^ m + s_rem) +
          k * (q_fn a).val * (N * 5 ^ (m - 1)) +
          (k * (w' a % 5) * 5 ^ m + N * (k * (rem_fn a / 5))) =
          (((j.val + 1) * (q_fn a).val + c_lookup c_a j.val + k * (w' a % 5)) * 5 ^ m + s_rem) +
          N * (k * (q_fn a).val * 5 ^ (m - 1) + k * (rem_fn a / 5)) := by ring
      rw [h3, Nat.add_mul_mod_self_left]
    rw [hexp]
    exact div_pow_mod_pow_succ (by decide) _ _ hs_rem_lt
  have hq0_zero : (q_fn 0).val = 0 := hw'0_div
  have hexists_jk : ∃ (j : Fin 3) (k_nat : ℕ),
      ∀ a : Fin 3,
        1 ≤ ((((j.val + 1) + k_nat * 5 ^ m) * w' a) % N) / 5 ^ m ∧
        ((((j.val + 1) + k_nat * 5 ^ m) * w' a) % N) / 5 ^ m ≤ 3 := by
    by_cases hsame2 : w' 2 % 5 = s_class.val + 1
    · obtain ⟨j, k, hk_good⟩ := bs5_decidable_same_class s_class c0 (q_fn 1) c1 (q_fn 2) c2
      refine ⟨j, k.val, fun a => ?_⟩
      dsimp at hk_good
      have ha012 : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
      rcases ha012 with rfl | rfl | rfl
      · rw [h_eval_digit 0 c0 hc0 j k.val, hq0_zero, mul_zero, zero_add, ← hs_val]
        exact ⟨hk_good.1, hk_good.2.1⟩
      · rw [h_eval_digit 1 c1 hc1 j k.val, hw'1_mod5]
        exact ⟨hk_good.2.2.1, hk_good.2.2.2.1⟩
      · rw [h_eval_digit 2 c2 hc2 j k.val, hsame2]
        exact ⟨hk_good.2.2.2.2.1, hk_good.2.2.2.2.2⟩
    · obtain ⟨j, k0, hk_comp⟩ := bs5_decidable_compression s_class c0 (q_fn 1) c1
      dsimp at hk_comp
      let step_k : ℕ := if s_class.val = 0 then 1 else 3
      have hw'2_12 : w' 2 % 5 = 1 ∨ w' 2 % 5 = 2 := by rw [hw'_mod5 2]; exact hv_mod5 (perm 2)
      let base2 : ℕ := ((j.val + 1) * (q_fn 2).val + c_lookup c2 j.val + k0.val * (w' 2 % 5)) % 5
      let next2 : ℕ := ((j.val + 1) * (q_fn 2).val + c_lookup c2 j.val + (k0.val + step_k) * (w' 2 % 5)) % 5
      have hstep_prod : (step_k * (w' 2 % 5)) % 5 = 2 ∨ (step_k * (w' 2 % 5)) % 5 = 3 := by
        have hs_lt2 : s_class.val < 2 := s_class.isLt
        dsimp [step_k]
        rcases hw'2_12 with h2_1 | h2_2
        · have hs1 : s_class.val = 1 := by omega
          rw [if_neg (by omega), h2_1]; right; rfl
        · have hs0 : s_class.val = 0 := by omega
          rw [if_pos hs0, h2_2]; left; rfl
      have h_one_good : (1 ≤ base2 ∧ base2 ≤ 3) ∨ (1 ≤ next2 ∧ next2 ≤ 3) := by
        have hstep : next2 = (base2 + (step_k * (w' 2 % 5)) % 5) % 5 := by
          dsimp [base2, next2]
          have h1 : (j.val + 1) * (q_fn 2).val + c_lookup c2 j.val + (k0.val + step_k) * (w' 2 % 5) =
              ((j.val + 1) * (q_fn 2).val + c_lookup c2 j.val + k0.val * (w' 2 % 5)) +
              step_k * (w' 2 % 5) := by ring
          rw [h1, Nat.add_mod]
        have hb_lt : base2 < 5 := Nat.mod_lt _ (by decide)
        rcases hstep_prod with hp2 | hp3
        · rw [hp2] at hstep; omega
        · rw [hp3] at hstep; omega
      rcases h_one_good with hbase | hnext
      · refine ⟨j, k0.val, fun a => ?_⟩
        have ha012 : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
        rcases ha012 with rfl | rfl | rfl
        · rw [h_eval_digit 0 c0 hc0 j k0.val, hq0_zero, mul_zero, zero_add, ← hs_val]
          exact ⟨hk_comp.1, hk_comp.2.1⟩
        · rw [h_eval_digit 1 c1 hc1 j k0.val, hw'1_mod5]
          exact ⟨hk_comp.2.2.1, hk_comp.2.2.2.1⟩
        · rw [h_eval_digit 2 c2 hc2 j k0.val]
          exact hbase
      · refine ⟨j, k0.val + step_k, fun a => ?_⟩
        have ha012 : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
        rcases ha012 with rfl | rfl | rfl
        · rw [h_eval_digit 0 c0 hc0 j (k0.val + step_k), hq0_zero, mul_zero, zero_add, ← hs_val]
          exact ⟨hk_comp.2.2.2.2.1, hk_comp.2.2.2.2.2.1⟩
        · rw [h_eval_digit 1 c1 hc1 j (k0.val + step_k), hw'1_mod5]
          exact ⟨hk_comp.2.2.2.2.2.2.1, hk_comp.2.2.2.2.2.2.2⟩
        · rw [h_eval_digit 2 c2 hc2 j (k0.val + step_k)]
          exact hnext
  obtain ⟨j, k_nat, hjk⟩ := hexists_jk
  let lam₁ : ℕ := (j.val + 1) + k_nat * 5 ^ m
  have hlam₁_not : ¬ (5 ∣ lam₁) := by
    intro hdvd
    have hdvd_pow : 5 ∣ k_nat * 5 ^ m := dvd_mul_of_dvd_right (dvd_pow_self 5 (by omega)) _
    have hdvd_j : 5 ∣ (j.val + 1) := (Nat.dvd_add_left hdvd_pow).mp hdvd
    have hj_lt : j.val < 3 := j.isLt
    have := Nat.le_of_dvd (by omega) hdvd_j
    omega
  let lam : ℕ := lam₁ * mu₀
  have hlam_not : ¬ (5 ∣ lam) := by
    intro hdvd
    rcases hp5.dvd_mul.mp hdvd with h1 | h2
    · exact hlam₁_not h1
    · exact hmu₀_not h2
  refine ⟨lam, hlam_not, fun a => ?_⟩
  apply hv_to_d lam a hlam_not
  let a' : Fin 3 := perm.symm a
  have hua' : u a' = v a := by dsimp [u, a']; simp
  have hmod_eq : (lam * v a) % N = (lam₁ * w' a') % N := by
    rw [← hua']
    dsimp [lam, w']
    rw [Nat.mul_mod lam₁, Nat.mod_mod, ← Nat.mul_mod, mul_assoc]
  rw [hmod_eq]
  exact hjk a'

private lemma lrc_nat_four (w : Fin 4 → ℕ) (hw : ∀ i : Fin 4, 0 < w i)
    (hgcd : Finset.univ.gcd w = 1) (hdvd5 : ∃ i : Fin 4, 5 ∣ w i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 4, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((4 + 1 : ℕ) : ℝ) := by
  have hp5 : Nat.Prime 5 := by decide
  have hex := fun i => exists_pow_mul_not_dvd (p := 5) (by decide) (w i) (hw i)
  let e : Fin 4 → ℕ := fun i => Classical.choose (hex i)
  let u : Fin 4 → ℕ := fun i => Classical.choose (Classical.choose_spec (hex i))
  have hu_spec : ∀ i, 0 < u i ∧ ¬ (5 ∣ u i) ∧ w i = 5 ^ (e i) * u i :=
    fun i => Classical.choose_spec (Classical.choose_spec (hex i))
  have hu_not : ∀ i, ¬ (5 ∣ u i) := fun i => (hu_spec i).2.1
  have hw_decomp : ∀ i, w i = 5 ^ (e i) * u i := fun i => (hu_spec i).2.2
  let m : ℕ := Finset.univ.sup e
  have he_le : ∀ i, e i ≤ m := fun i => Finset.le_sup (Finset.mem_univ i)
  have hm_ge : 1 ≤ m := by
    obtain ⟨i₀, hi₀⟩ := hdvd5
    have he_pos : 1 ≤ e i₀ := by
      rcases Nat.eq_zero_or_pos (e i₀) with h0 | hpos
      · exfalso
        rw [hw_decomp i₀, h0, pow_zero, one_mul] at hi₀
        exact hu_not i₀ hi₀
      · exact hpos
    exact le_trans he_pos (he_le i₀)
  have h5_cast : (((4 + 1 : ℕ) : ℝ)) = (5 : ℝ) := by norm_num
  rw [h5_cast]
  by_cases hlevels : ∀ j < m, (Finset.univ.filter (fun i : Fin 4 => e i = j)).card ≤ (5 - 1) / 2
  · obtain ⟨lam, hlam_not, hstep⟩ := prime_filtering_step hp5 (by decide) hm_ge e u hu_not hlevels m le_rfl
    refine prime_filtering_finish hp5 (by decide) w e u hu_not hw_decomp he_le lam hlam_not ?_
    intro i hlt
    rw [hw_decomp i]
    exact hstep i (by omega) hlt
  · simp only [not_forall, not_le] at hlevels
    obtain ⟨j₀, hj₀_lt, hj₀_card⟩ := hlevels
    let S₀ : Finset (Fin 4) := Finset.univ.filter (fun i => e i = 0)
    let Sₘ : Finset (Fin 4) := Finset.univ.filter (fun i => e i = m)
    let Sj₀ : Finset (Fin 4) := Finset.univ.filter (fun i => e i = j₀)
    have hS₀_ne : S₀.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have hall_dvd : ∀ i : Fin 4, 5 ∣ w i := by
        intro i
        have hei_ne : e i ≠ 0 := by
          intro h0
          have : i ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h0⟩
          rw [hemp] at this; exact Finset.notMem_empty i this
        rw [hw_decomp i]
        exact dvd_mul_of_dvd_left (dvd_pow_self 5 hei_ne) _
      have hdvd_gcd : 5 ∣ Finset.univ.gcd w := Finset.dvd_gcd (fun i _ => hall_dvd i)
      rw [hgcd] at hdvd_gcd
      have := Nat.le_of_dvd zero_lt_one hdvd_gcd
      omega
    have hSₘ_ne : Sₘ.Nonempty := by
      obtain ⟨i_max, _, hi_max⟩ := Finset.exists_max_image Finset.univ e ⟨0, Finset.mem_univ 0⟩
      have he_max : e i_max = m := le_antisymm (he_le i_max) (Finset.sup_le fun i _ => hi_max i (Finset.mem_univ i))
      exact ⟨i_max, Finset.mem_filter.mpr ⟨Finset.mem_univ i_max, he_max⟩⟩
    have hdisj_jm : Disjoint Sj₀ Sₘ := by
      rw [Finset.disjoint_filter]
      intro i _ h1 h2; omega
    have hcard_Sj₀ : 3 ≤ Sj₀.card := by
      change (5 - 1) / 2 < Sj₀.card at hj₀_card
      omega
    have hcard_Sₘ : 1 ≤ Sₘ.card := Finset.card_pos.mpr hSₘ_ne
    have hsum_le : Sj₀.card + Sₘ.card ≤ 4 := by
      rw [← Finset.card_union_of_disjoint hdisj_jm]
      exact le_trans (Finset.card_le_univ _) (by simp)
    have hSj₀_eq3 : Sj₀.card = 3 := by omega
    have hunion_univ : Sj₀ ∪ Sₘ = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_union_of_disjoint hdisj_jm, Finset.card_fin]
      omega
    have hj₀_zero : j₀ = 0 := by
      obtain ⟨i₀, hi₀⟩ := hS₀_ne
      have hi₀_mem : i₀ ∈ Sj₀ ∪ Sₘ := by rw [hunion_univ]; exact Finset.mem_univ i₀
      have hei₀ : e i₀ = 0 := (Finset.mem_filter.mp hi₀).2
      rcases Finset.mem_union.mp hi₀_mem with h1 | h2
      · have := (Finset.mem_filter.mp h1).2; omega
      · have := (Finset.mem_filter.mp h2).2; omega
    subst hj₀_zero
    let emb := S₀.orderEmbOfFin hSj₀_eq3
    let d : Fin 3 → ℕ := fun a => w (emb a)
    have hd_not : ∀ a : Fin 3, ¬ (5 ∣ d a) := by
      intro a
      have hmem : emb a ∈ S₀ := Finset.orderEmbOfFin_mem S₀ hSj₀_eq3 a
      have he0 : e (emb a) = 0 := (Finset.mem_filter.mp hmem).2
      dsimp [d]
      rw [hw_decomp (emb a), he0, pow_zero, one_mul]
      exact hu_not (emb a)
    obtain ⟨lam, hlam_not, hlam_good⟩ := bs5_three_unit_runners hm_ge d hd_not
    refine prime_filtering_finish hp5 (by decide) w e u hu_not hw_decomp he_le lam hlam_not ?_
    intro i hlt
    have hi_in_union : i ∈ Sj₀ ∪ Sₘ := by rw [hunion_univ]; exact Finset.mem_univ i
    have hi_not_Sm : i ∉ Sₘ := by
      intro hm_in
      have := (Finset.mem_filter.mp hm_in).2
      omega
    have hi_in_S₀ : i ∈ S₀ := (Finset.mem_union.mp hi_in_union).resolve_right hi_not_Sm
    have hi_range : i ∈ Set.range emb := by
      rw [Finset.range_orderEmbOfFin]
      exact hi_in_S₀
    obtain ⟨a, ha⟩ := hi_range
    rw [← ha]
    exact hlam_good a

private lemma lrc_six_three_mult_seven (w : Fin 6 → ℕ) (hw : ∀ i : Fin 6, 0 < w i)
    (hdvd7 : ∃ i : Fin 6, 7 ∣ w i)
    (hcard3 : (Finset.univ.filter (fun i : Fin 6 => 7 ∣ w i)).card = 3) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 6, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((6 + 1 : ℕ) : ℝ) := by
  have hp7 : Nat.Prime 7 := by decide
  have hex := fun i => exists_pow_mul_not_dvd (p := 7) (by decide) (w i) (hw i)
  let e : Fin 6 → ℕ := fun i => Classical.choose (hex i)
  let u : Fin 6 → ℕ := fun i => Classical.choose (Classical.choose_spec (hex i))
  have hu_spec : ∀ i, 0 < u i ∧ ¬ (7 ∣ u i) ∧ w i = 7 ^ (e i) * u i :=
    fun i => Classical.choose_spec (Classical.choose_spec (hex i))
  have hu_not : ∀ i, ¬ (7 ∣ u i) := fun i => (hu_spec i).2.1
  have hw_decomp : ∀ i, w i = 7 ^ (e i) * u i := fun i => (hu_spec i).2.2
  let m : ℕ := Finset.univ.sup e
  have he_le : ∀ i, e i ≤ m := fun i => Finset.le_sup (Finset.mem_univ i)
  have hm_ge : 1 ≤ m := by
    obtain ⟨i₀, hi₀⟩ := hdvd7
    have he_pos : 1 ≤ e i₀ := by
      rcases Nat.eq_zero_or_pos (e i₀) with h0 | hpos
      · exfalso
        rw [hw_decomp i₀, h0, pow_zero, one_mul] at hi₀
        exact hu_not i₀ hi₀
      · exact hpos
    exact le_trans he_pos (he_le i₀)
  let S₀ : Finset (Fin 6) := Finset.univ.filter (fun i => e i = 0)
  have hS₀_eq_sdiff : S₀ = Finset.univ \ (Finset.univ.filter (fun i : Fin 6 => 7 ∣ w i)) := by
    ext i
    simp only [S₀, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro he0 hdvd
      rw [hw_decomp i, he0, pow_zero, one_mul] at hdvd
      exact hu_not i hdvd
    · intro hndvd
      rcases Nat.eq_zero_or_pos (e i) with h0 | hpos
      · exact h0
      · exfalso
        apply hndvd
        rw [hw_decomp i]
        exact dvd_mul_of_dvd_left (dvd_pow_self 7 (by omega)) _
  have hS₀_card : S₀.card = 3 := by
    rw [hS₀_eq_sdiff, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_fin, hcard3]
  let Sₘ : Finset (Fin 6) := Finset.univ.filter (fun i => e i = m)
  have hSₘ_ne : Sₘ.Nonempty := by
    obtain ⟨i_max, _, hi_max⟩ := Finset.exists_max_image Finset.univ e ⟨0, Finset.mem_univ 0⟩
    have he_max : e i_max = m := le_antisymm (he_le i_max) (Finset.sup_le fun i _ => hi_max i (Finset.mem_univ i))
    exact ⟨i_max, Finset.mem_filter.mpr ⟨Finset.mem_univ i_max, he_max⟩⟩
  have hcard_Sₘ : 1 ≤ Sₘ.card := Finset.card_pos.mpr hSₘ_ne
  have hlevels : ∀ j < m, (Finset.univ.filter (fun i : Fin 6 => e i = j)).card ≤ (7 - 1) / 2 := by
    intro j hj_lt
    rcases eq_or_ne j 0 with rfl | hj0
    · change S₀.card ≤ (7 - 1) / 2
      omega
    · let Sj : Finset (Fin 6) := Finset.univ.filter (fun i => e i = j)
      have hdisj0j : Disjoint S₀ Sj := by
        rw [Finset.disjoint_filter]
        intro i _ h1 h2; omega
      have hdisj_m : Disjoint (S₀ ∪ Sj) Sₘ := by
        rw [Finset.disjoint_left]
        intro i hi_u hi_m
        have hem : e i = m := (Finset.mem_filter.mp hi_m).2
        rcases Finset.mem_union.mp hi_u with hi0 | hij
        · have := (Finset.mem_filter.mp hi0).2; omega
        · have := (Finset.mem_filter.mp hij).2; omega
      have htot : S₀.card + Sj.card + Sₘ.card ≤ 6 := by
        rw [← Finset.card_union_of_disjoint hdisj0j, ← Finset.card_union_of_disjoint hdisj_m]
        exact le_trans (Finset.card_le_univ _) (by simp)
      change Sj.card ≤ (7 - 1) / 2
      omega
  have h7_cast : (((6 + 1 : ℕ) : ℝ)) = (7 : ℝ) := by norm_num
  rw [h7_cast]
  obtain ⟨lam, hlam_not, hstep⟩ := prime_filtering_step hp7 (by decide) hm_ge e u hu_not hlevels m le_rfl
  refine prime_filtering_finish hp7 (by decide) w e u hu_not hw_decomp he_le lam hlam_not ?_
  intro i hlt
  rw [hw_decomp i]
  exact hstep i (by omega) hlt

/- ### Module 3: Generalized Prime-Multiplicity Shift Sieve & Universal Bounds -/

private lemma strictMono_gap_bound {r : ℕ} (hr : 1 ≤ r) (f : Fin r → ℝ) {δ : ℝ}
    (hgap : ∀ i j : Fin r, i < j → δ ≤ f j - f i) :
    ((r - 1 : ℕ) : ℝ) * δ ≤ f ⟨r - 1, by omega⟩ - f ⟨0, by omega⟩ := by
  have hind : ∀ m : ℕ, (hm : m < r) → (m : ℝ) * δ ≤ f ⟨m, hm⟩ - f ⟨0, by omega⟩ := by
    intro m
    induction m with
    | zero =>
      intro _
      simp
    | succ m ih =>
      intro hm1
      have hm : m < r := by omega
      have h1 := ih hm
      have hlt : (⟨m, hm⟩ : Fin r) < ⟨m + 1, hm1⟩ := Fin.mk_lt_mk.mpr (by omega)
      have h2 := hgap ⟨m, hm⟩ ⟨m + 1, hm1⟩ hlt
      push_cast
      linarith
  exact hind (r - 1) (by omega)

private lemma lrc_nat_prime_multiplicity_sieve {k q m₀ : ℕ} (hk : 3 ≤ k) (hq : Nat.Prime q)
    (hm₀_ge : 1 ≤ m₀)
    (hcap : (k - m₀) * (1 + (2 * q - 1) / (k + 1)) < q)
    (w : Fin k → ℕ) (hw : ∀ i, 0 < w i) (hmono : StrictMono w) (hgcd : Finset.univ.gcd w = 1)
    (hmult : m₀ ≤ (Finset.univ.filter (fun i : Fin k => q ∣ w i)).card)
    (h_smaller : ∀ (m : ℕ), 1 ≤ m → m < k → ∀ (u : Fin m → ℕ),
      (∀ i : Fin m, 0 < u i) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  have hq2 : 2 ≤ q := hq.two_le
  have hq_pos : (0 : ℝ) < (q : ℝ) := by positivity
  let Mset : Finset (Fin k) := Finset.univ.filter (fun i => q ∣ w i)
  have hM_lt : Mset.card < k := by
    by_contra hge
    have heq_univ : Mset = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_fin]; omega
    have hdvd_all : ∀ i : Fin k, q ∣ w i := by
      intro i
      have : i ∈ Mset := by rw [heq_univ]; exact Finset.mem_univ i
      exact (Finset.mem_filter.mp this).2
    have hdvd_gcd : q ∣ Finset.univ.gcd w := Finset.dvd_gcd (fun i _ => hdvd_all i)
    rw [hgcd] at hdvd_gcd
    have := Nat.le_of_dvd zero_lt_one hdvd_gcd
    omega
  let m_div : ℕ := Mset.card
  have hm_ge : 1 ≤ m_div := le_trans hm₀_ge hmult
  let embM := Mset.orderEmbOfFin rfl
  let u_sub : Fin m_div → ℕ := fun j => w (embM j)
  have hu_pos : ∀ j, 0 < u_sub j := fun j => hw (embM j)
  have hu_mono : StrictMono u_sub := hmono.comp embM.strictMono
  obtain ⟨t₀, ht₀_nonneg, ht₀⟩ := h_smaller m_div hm_ge hM_lt u_sub hu_pos hu_mono
  let candT : Fin q → ℝ := fun s => t₀ + (s.val : ℝ) / (q : ℝ)
  let badShifts : Fin k → Finset (Fin q) := fun i =>
    Finset.univ.filter (fun s : Fin q =>
      dist ((candT s * (w i : ℝ) : ℝ) : UnitAddCircle) 0 < 1 / ((k + 1 : ℕ) : ℝ))
  have hbad_per_runner : ∀ i ∈ Finset.univ \ Mset,
      (badShifts i).card ≤ 1 + (2 * q - 1) / (k + 1) := by
    intro i hi_sdiff
    have hi_not_dvd : ¬ (q ∣ w i) := by
      intro hdvd
      exact (Finset.mem_sdiff.mp hi_sdiff).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hdvd⟩)
    by_cases hemp : (badShifts i) = ∅
    · rw [hemp, Finset.card_empty]
      exact Nat.zero_le _
    · have hne_bad : (badShifts i).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
      let xFn : Fin q → ℝ := fun s =>
        candT s * (w i : ℝ) - (round (candT s * (w i : ℝ)) : ℝ)
      have hx_lt : ∀ s ∈ badShifts i, |xFn s| < 1 / ((k + 1 : ℕ) : ℝ) := by
        intro s hs
        have hlt := (Finset.mem_filter.mp hs).2
        rw [dist_zero_right, UnitAddCircle.norm_eq] at hlt
        exact hlt
      have hx_sep : ∀ s₁ s₂ : Fin q, s₁ ≠ s₂ → 1 / (q : ℝ) ≤ |xFn s₁ - xFn s₂| := by
        intro s₁ s₂ hs_ne
        let Z : ℤ := ((s₁.val : ℤ) - (s₂.val : ℤ)) * (w i : ℤ) -
          (q : ℤ) * (round (candT s₁ * (w i : ℝ)) - round (candT s₂ * (w i : ℝ)))
        have hZ_real : (q : ℝ) * (xFn s₁ - xFn s₂) = (Z : ℝ) := by
          dsimp [xFn, candT, Z]
          push_cast
          field_simp [ne_of_gt hq_pos]
          ring
        have hZ_ne : Z ≠ 0 := by
          intro hZ0
          have heq_z : ((s₁.val : ℤ) - (s₂.val : ℤ)) * (w i : ℤ) =
              (q : ℤ) * (round (candT s₁ * (w i : ℝ)) - round (candT s₂ * (w i : ℝ))) :=
            sub_eq_zero.mp hZ0
          have habs_eq := congr_arg Int.natAbs heq_z
          rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at habs_eq
          have hdvd_mul : q ∣ ((s₁.val : ℤ) - (s₂.val : ℤ)).natAbs * w i :=
            ⟨_, habs_eq⟩
          have hdvd_diff : q ∣ ((s₁.val : ℤ) - (s₂.val : ℤ)).natAbs :=
            (hq.dvd_mul.mp hdvd_mul).resolve_right hi_not_dvd
          have hval_ne : s₁.val ≠ s₂.val := fun hv => hs_ne (Fin.ext hv)
          have h1 := s₁.isLt
          have h2 := s₂.isLt
          have hdiff_pos : 0 < ((s₁.val : ℤ) - (s₂.val : ℤ)).natAbs := by omega
          have hdiff_lt : ((s₁.val : ℤ) - (s₂.val : ℤ)).natAbs < q := by omega
          have := Nat.le_of_dvd hdiff_pos hdvd_diff
          omega
        have hZ_abs : (1 : ℝ) ≤ |(Z : ℝ)| := by
          have : (1 : ℤ) ≤ |Z| := Int.one_le_abs hZ_ne
          exact_mod_cast this
        rw [← hZ_real, abs_mul, abs_of_pos hq_pos] at hZ_abs
        rw [div_le_iff₀ hq_pos]
        linarith
      have hx_inj : Set.InjOn xFn (badShifts i) := by
        intro s₁ _ s₂ _ heq
        by_contra hne
        have hsep := hx_sep s₁ s₂ hne
        rw [heq, sub_self, abs_zero] at hsep
        have : (0 : ℝ) < 1 / (q : ℝ) := by positivity
        linarith
      let imgX : Finset ℝ := (badShifts i).image xFn
      let r : ℕ := imgX.card
      have hr_eq : r = (badShifts i).card := Finset.card_image_of_injOn hx_inj
      have hr_ge : 1 ≤ r := by rw [hr_eq]; exact Finset.card_pos.mpr hne_bad
      let embX := imgX.orderEmbOfFin rfl
      have hgap : ∀ a b : Fin r, a < b → 1 / (q : ℝ) ≤ embX b - embX a := by
        intro a b hab
        have ha_mem : embX a ∈ imgX := Finset.orderEmbOfFin_mem imgX rfl a
        have hb_mem : embX b ∈ imgX := Finset.orderEmbOfFin_mem imgX rfl b
        obtain ⟨s₁, _, hs₁⟩ := Finset.mem_image.mp ha_mem
        obtain ⟨s₂, _, hs₂⟩ := Finset.mem_image.mp hb_mem
        have hab_lt : embX a < embX b := embX.strictMono hab
        have hs_ne : s₁ ≠ s₂ := fun h => by rw [h, hs₂] at hs₁; linarith
        have hsep := hx_sep s₂ s₁ hs_ne.symm
        rw [hs₁, hs₂, abs_of_pos (sub_pos.mpr hab_lt)] at hsep
        exact hsep
      have htele := strictMono_gap_bound hr_ge embX hgap
      have h0_mem : embX ⟨0, by omega⟩ ∈ imgX := Finset.orderEmbOfFin_mem imgX rfl ⟨0, by omega⟩
      have hlast_mem : embX ⟨r - 1, by omega⟩ ∈ imgX :=
        Finset.orderEmbOfFin_mem imgX rfl ⟨r - 1, by omega⟩
      obtain ⟨s_lo, hs_lo_mem, hs_lo_eq⟩ := Finset.mem_image.mp h0_mem
      obtain ⟨s_hi, hs_hi_mem, hs_hi_eq⟩ := Finset.mem_image.mp hlast_mem
      have hlo_bound := (abs_lt.mp (hx_lt s_lo hs_lo_mem)).1
      have hhi_bound := (abs_lt.mp (hx_lt s_hi hs_hi_mem)).2
      rw [hs_lo_eq] at hlo_bound
      rw [hs_hi_eq] at hhi_bound
      have hspan_lt : embX ⟨r - 1, by omega⟩ - embX ⟨0, by omega⟩ < 2 / ((k + 1 : ℕ) : ℝ) := by
        have : 2 / ((k + 1 : ℕ) : ℝ) = 1 / ((k + 1 : ℕ) : ℝ) - (-(1 / ((k + 1 : ℕ) : ℝ))) := by ring
        linarith
      have hr_ineq_real : ((r - 1 : ℕ) : ℝ) * (1 / (q : ℝ)) < 2 / ((k + 1 : ℕ) : ℝ) :=
        lt_of_le_of_lt htele hspan_lt
      have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hmul_real : ((r - 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) < 2 * (q : ℝ) := by
        rw [mul_one_div, div_lt_div_iff₀ hq_pos hk1_pos] at hr_ineq_real
        linarith
      have hmul_nat : (r - 1) * (k + 1) < 2 * q := by exact_mod_cast hmul_real
      have hmul_le : (r - 1) * (k + 1) ≤ 2 * q - 1 := by omega
      have hdiv_le : r - 1 ≤ (2 * q - 1) / (k + 1) :=
        (Nat.le_div_iff_mul_le (by omega : 0 < k + 1)).mpr hmul_le
      rw [← hr_eq]
      omega
  let allBad : Finset (Fin q) := (Finset.univ \ Mset).biUnion badShifts
  have hallBad_lt : allBad.card < q := by
    have hsdiff_card : (Finset.univ \ Mset).card = k - m_div := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ Mset), Finset.card_fin]
    have hsub_le : k - m_div ≤ k - m₀ := Nat.sub_le_sub_left hmult k
    calc
      allBad.card ≤ ∑ i ∈ Finset.univ \ Mset, (badShifts i).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ Finset.univ \ Mset, (1 + (2 * q - 1) / (k + 1)) :=
        Finset.sum_le_sum hbad_per_runner
      _ = (k - m_div) * (1 + (2 * q - 1) / (k + 1)) := by
        rw [Finset.sum_const, hsdiff_card, smul_eq_mul]
      _ ≤ (k - m₀) * (1 + (2 * q - 1) / (k + 1)) := Nat.mul_le_mul_right _ hsub_le
      _ < q := hcap
  have hexists_s : (Finset.univ \ allBad).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : (Finset.univ : Finset (Fin q)) ⊆ allBad := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_fin] at hcard
    omega
  obtain ⟨s₀, hs₀⟩ := hexists_s
  have hs₀_not_bad : s₀ ∉ allBad := (Finset.mem_sdiff.mp hs₀).2
  refine ⟨candT s₀, by dsimp [candT]; positivity, fun i => ?_⟩
  by_cases hiM : i ∈ Mset
  · have hq_dvd : q ∣ w i := (Finset.mem_filter.mp hiM).2
    let w_div : ℕ := w i / q
    have hw_mul : q * w_div = w i := Nat.mul_div_cancel' hq_dvd
    have hw_real : (q : ℝ) * (w_div : ℝ) = (w i : ℝ) := by exact_mod_cast hw_mul
    let prodReal : ℝ := candT s₀ * (w i : ℝ)
    let baseReal : ℝ := t₀ * (w i : ℝ)
    have hmk_eq : (prodReal : UnitAddCircle) = (baseReal : UnitAddCircle) := by
      have hsplit : prodReal = baseReal + (((s₀.val * w_div : ℕ) : ℤ) : ℝ) := by
        dsimp [prodReal, baseReal, candT]
        rw [← hw_real]
        push_cast
        field_simp [ne_of_gt hq_pos]
      rw [hsplit, QuotientAddGroup.mk_add, unitAddCircle_int_cast_eq_zero, add_zero]
    change dist (prodReal : UnitAddCircle) 0 ≥ _
    rw [hmk_eq]
    have hi_range : i ∈ Set.range embM := by
      rw [Finset.range_orderEmbOfFin]
      exact hiM
    obtain ⟨j, hj⟩ := hi_range
    have hbase_eq : baseReal = t₀ * (u_sub j : ℝ) := by
      dsimp [baseReal, u_sub]
      rw [hj]
    have hm_le : ((m_div + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : m_div + 1 ≤ k + 1)
    have hdist_sub : dist ((baseReal : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m_div + 1 : ℕ) : ℝ) := by
      rw [hbase_eq]
      exact ht₀ j
    exact le_trans (one_div_le_one_div_of_le (by positivity) hm_le) hdist_sub
  · have hi_sdiff : i ∈ Finset.univ \ Mset := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiM⟩
    have hs_not_i : s₀ ∉ badShifts i :=
      fun h => hs₀_not_bad (Finset.mem_biUnion.mpr ⟨i, hi_sdiff, h⟩)
    have hnot_lt : ¬ (dist ((candT s₀ * (w i : ℝ) : ℝ) : UnitAddCircle) 0 < 1 / ((k + 1 : ℕ) : ℝ)) :=
      fun hlt => hs_not_i (Finset.mem_filter.mpr ⟨Finset.mem_univ s₀, hlt⟩)
    exact le_of_not_gt hnot_lt

private lemma odd_prime_cap_le {k q : ℕ} (hk : 5 ≤ k) (hq : Nat.Prime q) (hq3 : 3 ≤ q) :
    (k - (k - 2)) * (1 + (2 * q - 1) / (k + 1)) < q := by
  have hsub : k - (k - 2) = 2 := by omega
  have hdiv_le : (2 * q - 1) / (k + 1) ≤ (2 * q - 1) / 6 :=
    Nat.div_le_div_left (by omega : 6 ≤ k + 1) (by decide : 0 < 6)
  have hq4 : q ≠ 4 := fun h => absurd (h ▸ hq) (by decide)
  rw [hsub]
  omega

private lemma prime_ge_seven_cap_le {k q : ℕ} (hk : 7 ≤ k) (hq : Nat.Prime q) (hq7 : 7 ≤ q) :
    (k - (k - 3)) * (1 + (2 * q - 1) / (k + 1)) < q := by
  have hsub : k - (k - 3) = 3 := by omega
  have hdiv_le : (2 * q - 1) / (k + 1) ≤ (2 * q - 1) / 8 :=
    Nat.div_le_div_left (by omega : 8 ≤ k + 1) (by decide : 0 < 8)
  have hq9 : q ≠ 9 := fun h => absurd (h ▸ hq) (by decide)
  rw [hsub]
  omega

/- ### Module 4: Zero-`def` Malikiosis-Santos-Schymura GCD-Sum Bound -/

private lemma mss_gcd_eq_nat_gcd (a b : ℕ) : GCDMonoid.gcd a b = Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (GCDMonoid.gcd_dvd_left a b) (GCDMonoid.gcd_dvd_right a b)
  · exact GCDMonoid.dvd_gcd (Nat.gcd_dvd_left a b) (GCDMonoid.gcd_dvd_right a b)

private lemma finset_gcd_bezout {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℕ) :
    ∃ c : ι → ℤ, ((s.gcd w : ℕ) : ℤ) = ∑ i ∈ s, c i * (w i : ℤ) := by
  induction s using Finset.cons_induction with
  | empty =>
    exact ⟨fun _ => 0, by simp⟩
  | cons a s has ih =>
    obtain ⟨c, hc⟩ := ih
    rw [Finset.gcd_cons, mss_gcd_eq_nat_gcd]
    let A := Nat.gcdA (w a) (s.gcd w)
    let B := Nat.gcdB (w a) (s.gcd w)
    refine ⟨fun i => if i = a then A else B * c i, ?_⟩
    rw [Finset.sum_cons]
    dsimp only
    rw [if_pos rfl]
    have hsum : ∑ x ∈ s, (if x = a then A else B * c x) * (w x : ℤ) =
        B * ∑ x ∈ s, c x * (w x : ℤ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hne : x ≠ a := fun h => has (h ▸ hx)
      rw [if_neg hne, mul_assoc]
    rw [hsum, ← hc]
    have hbez := Nat.gcd_eq_gcd_ab (w a) (s.gcd w)
    linarith

private lemma exists_short_nonproportional_vec {k : ℕ} (hk : 3 ≤ k) {w : Fin k → ℕ}
    (hw : ∀ i, 0 < w i) (hgcd : Finset.univ.gcd w = 1)
    (hsum : (Nat.choose (k + 1) 2) ^ (k - 1) <
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅, S.gcd w) :
    ∃ (q : Fin k → ℤ) (β : ℝ),
      (¬ ∃ γ : ℝ, ∀ i : Fin k, (q i : ℝ) = γ * (w i : ℝ)) ∧
      (∀ i : Fin k, |(q i : ℝ) + β * (w i : ℝ)| ≤ 2 / ((k : ℝ) * ((k : ℝ) + 1))) := by
  obtain ⟨c, hc0⟩ := finset_gcd_bezout (Finset.univ : Finset (Fin k)) w
  rw [hgcd] at hc0
  have hc : ∑ i : Fin k, c i * (w i : ℤ) = 1 := hc0.symm
  let ℓ : ℕ := Nat.choose (k + 1) 2
  have hℓ_two : 2 * ℓ = k * (k + 1) := two_mul_choose_two k
  have hk_mul_pos : 0 < k * (k + 1) := Nat.mul_pos (by omega) (by omega)
  have hℓ_pos : 0 < ℓ := by omega
  have : NeZero ℓ := ⟨Nat.ne_of_gt hℓ_pos⟩
  let bLin : (Fin k → ZMod ℓ) → ZMod ℓ := fun y => ∑ i : Fin k, (c i : ZMod ℓ) * y i
  have hbLin_w : bLin (fun i => (w i : ZMod ℓ)) = 1 := by
    have h := congr_arg (Int.cast : ℤ → ZMod ℓ) hc
    simpa [bLin, Int.cast_sum, Int.cast_mul, Int.cast_natCast] using h
  have hbLin_add : ∀ (y : Fin k → ZMod ℓ) (t : ZMod ℓ),
      bLin (fun i => y i + t * (w i : ZMod ℓ)) = bLin y + t := by
    intro y t
    dsimp [bLin]
    have h1 : ∑ i : Fin k, (c i : ZMod ℓ) * (y i + t * (w i : ZMod ℓ)) =
        (∑ i : Fin k, (c i : ZMod ℓ) * y i) +
        t * (∑ i : Fin k, (c i : ZMod ℓ) * (w i : ZMod ℓ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [h1]
    change bLin y + t * bLin (fun i => (w i : ZMod ℓ)) = bLin y + t
    rw [hbLin_w, mul_one]
  have hbLin_sub : ∀ (y : Fin k → ZMod ℓ) (t : ZMod ℓ),
      bLin (fun i => y i - t * (w i : ZMod ℓ)) = bLin y - t := by
    intro y t
    have h := hbLin_add y (-t)
    simpa [sub_eq_add_neg, neg_mul] using h
  let kerEquiv : { u : Fin k → ZMod ℓ // bLin u = 0 } × ZMod ℓ ≃ (Fin k → ZMod ℓ) :=
    { toFun := fun p i => p.1.1 i + p.2 * (w i : ZMod ℓ)
      invFun := fun y => (⟨fun i => y i - bLin y * (w i : ZMod ℓ), by
        rw [hbLin_sub, sub_self]⟩, bLin y)
      left_inv := by
        rintro ⟨⟨u, hu⟩, t⟩
        have hL : bLin (fun i => u i + t * (w i : ZMod ℓ)) = t := by
          rw [hbLin_add, hu, zero_add]
        ext i
        · dsimp; rw [hL]; ring
        · dsimp; exact hL
      right_inv := by
        intro y; ext i; dsimp; ring }
  have hcard_ker : Fintype.card { u : Fin k → ZMod ℓ // bLin u = 0 } = ℓ ^ (k - 1) := by
    have hcard := Fintype.card_congr kerEquiv
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
    have hk_eq : ℓ ^ k = ℓ ^ (k - 1) * ℓ := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    rw [hk_eq] at hcard
    exact Nat.mul_right_cancel hℓ_pos hcard
  let NP : Finset (Finset (Fin k)) := (Finset.univ : Finset (Fin k)).powerset.erase ∅
  let Idx : Type := Σ S : { S : Finset (Fin k) // S ∈ NP }, Fin (S.1.gcd w)
  have hcard_idx : Fintype.card Idx = ∑ S ∈ NP, S.gcd w := by
    dsimp [Idx]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach NP (fun S => S.gcd w)
  have hsub_ne : ∀ {S : Finset (Fin k)}, S ∈ NP → S.Nonempty :=
    fun hS => Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1
  have hsub_gcd_pos : ∀ {S : Finset (Fin k)}, S ∈ NP → 0 < S.gcd w := by
    intro S hS
    obtain ⟨i₀, hi₀⟩ := hsub_ne hS
    have hdvd : S.gcd w ∣ w i₀ := Finset.gcd_dvd hi₀
    rcases Nat.eq_zero_or_pos (S.gcd w) with h0 | hpos
    · rw [h0, zero_dvd_iff] at hdvd
      exact absurd hdvd (Nat.ne_of_gt (hw i₀))
    · exact hpos
  let alphaVal : Idx → ℝ := fun x => (x.2.val : ℝ) / ((x.1.1.gcd w : ℕ) : ℝ)
  have halpha_nonneg : ∀ x : Idx, 0 ≤ alphaVal x := fun x => by dsimp [alphaVal]; positivity
  have halpha_lt_one : ∀ x : Idx, alphaVal x < 1 := by
    intro x
    dsimp [alphaVal]
    have hg : (0 : ℝ) < ((x.1.1.gcd w : ℕ) : ℝ) := Nat.cast_pos.mpr (hsub_gcd_pos x.1.2)
    rw [div_lt_one hg]
    exact Nat.cast_lt.mpr x.2.isLt
  let zVec : Idx → Fin k → ℤ := fun x i =>
    let g : ℕ := x.1.1.gcd w
    let q_div : ℕ := w i / g
    if i ∈ x.1.1 then - ((x.2.val : ℤ) * (q_div : ℤ))
    else ⌊(1 : ℝ) - alphaVal x * (w i : ℝ)⌋
  have hz_mem : ∀ (x : Idx) {i : Fin k}, i ∈ x.1.1 →
      (zVec x i : ℝ) + alphaVal x * (w i : ℝ) = 0 := by
    intro x i hi
    let g : ℕ := x.1.1.gcd w
    let q_div : ℕ := w i / g
    have hz : zVec x i = - ((x.2.val : ℤ) * (q_div : ℤ)) := by simp [zVec, hi, g, q_div]
    have hdvd : g ∣ w i := Finset.gcd_dvd hi
    have hmul : q_div * g = w i := Nat.div_mul_cancel hdvd
    have hg_pos : (0 : ℝ) < (g : ℝ) := Nat.cast_pos.mpr (hsub_gcd_pos x.1.2)
    have hmul_real : (q_div : ℝ) * (g : ℝ) = (w i : ℝ) := by exact_mod_cast hmul
    have ha : alphaVal x = (x.2.val : ℝ) / (g : ℝ) := rfl
    rw [hz, ha, ← hmul_real]
    push_cast
    field_simp [ne_of_gt hg_pos]
    ring
  have hz_not_mem : ∀ (x : Idx) {i : Fin k}, i ∉ x.1.1 →
      0 < (zVec x i : ℝ) + alphaVal x * (w i : ℝ) ∧
        (zVec x i : ℝ) + alphaVal x * (w i : ℝ) ≤ 1 := by
    intro x i hi
    dsimp [zVec]
    simp only [hi, ↓reduceIte]
    have h1 := Int.sub_one_lt_floor ((1 : ℝ) - alphaVal x * (w i : ℝ))
    have h2 := Int.floor_le ((1 : ℝ) - alphaVal x * (w i : ℝ))
    constructor <;> linarith
  have hz_Icc : ∀ (x : Idx) (i : Fin k),
      0 ≤ (zVec x i : ℝ) + alphaVal x * (w i : ℝ) ∧
        (zVec x i : ℝ) + alphaVal x * (w i : ℝ) ≤ 1 := by
    intro x i
    by_cases hi : i ∈ x.1.1
    · rw [hz_mem x hi]; exact ⟨le_rfl, zero_le_one⟩
    · obtain ⟨hpos, hle⟩ := hz_not_mem x hi; exact ⟨le_of_lt hpos, hle⟩
  have hz_zero_iff : ∀ (x : Idx) (i : Fin k),
      (zVec x i : ℝ) + alphaVal x * (w i : ℝ) = 0 ↔ i ∈ x.1.1 := by
    intro x i
    constructor
    · intro h0
      by_contra hi
      have hpos := (hz_not_mem x hi).1
      linarith
    · exact hz_mem x
  have hz_inj : ∀ {x₁ x₂ : Idx} {m : ℤ},
      (∀ i : Fin k, zVec x₁ i - zVec x₂ i = m * (w i : ℤ)) → x₁ = x₂ := by
    intro x₁ x₂ m hmod
    obtain ⟨i₁, hi₁⟩ := hsub_ne x₁.1.2
    obtain ⟨i₂, hi₂⟩ := hsub_ne x₂.1.2
    have hm_le : (m : ℝ) ≤ alphaVal x₂ - alphaVal x₁ := by
      have hz1 := hz_mem x₁ hi₁
      have hz2 := (hz_Icc x₂ i₁).1
      have hdiff : (zVec x₁ i₁ : ℝ) - (zVec x₂ i₁ : ℝ) = (m : ℝ) * (w i₁ : ℝ) := by
        exact_mod_cast hmod i₁
      have hw1 : (0 : ℝ) < (w i₁ : ℝ) := Nat.cast_pos.mpr (hw i₁)
      have hprod : 0 ≤ (alphaVal x₂ - alphaVal x₁ - (m : ℝ)) * (w i₁ : ℝ) := by linarith
      have hnonneg : 0 ≤ alphaVal x₂ - alphaVal x₁ - (m : ℝ) :=
        nonneg_of_mul_nonneg_left hprod hw1
      linarith
    have hm_ge : alphaVal x₂ - alphaVal x₁ ≤ (m : ℝ) := by
      have hz2 := hz_mem x₂ hi₂
      have hz1 := (hz_Icc x₁ i₂).1
      have hdiff : (zVec x₁ i₂ : ℝ) - (zVec x₂ i₂ : ℝ) = (m : ℝ) * (w i₂ : ℝ) := by
        exact_mod_cast hmod i₂
      have hw2 : (0 : ℝ) < (w i₂ : ℝ) := Nat.cast_pos.mpr (hw i₂)
      have hprod : 0 ≤ ((m : ℝ) - (alphaVal x₂ - alphaVal x₁)) * (w i₂ : ℝ) := by linarith
      have hnonneg : 0 ≤ (m : ℝ) - (alphaVal x₂ - alphaVal x₁) :=
        nonneg_of_mul_nonneg_left hprod hw2
      linarith
    have hm_eq : (m : ℝ) = alphaVal x₂ - alphaVal x₁ := le_antisymm hm_le hm_ge
    have ha1_0 := halpha_nonneg x₁
    have ha1_1 := halpha_lt_one x₁
    have ha2_0 := halpha_nonneg x₂
    have ha2_1 := halpha_lt_one x₂
    have hm_gt : ((-1 : ℤ) : ℝ) < (m : ℝ) := by push_cast; linarith
    have hm_lt : (m : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
    have hm_gt_int : (-1 : ℤ) < m := Int.cast_lt.mp hm_gt
    have hm_lt_int : m < 1 := Int.cast_lt.mp hm_lt
    have hm0 : m = 0 := by omega
    have halpha : alphaVal x₁ = alphaVal x₂ := by
      rw [hm0, Int.cast_zero] at hm_eq
      linarith
    have hz_eq : ∀ i : Fin k, zVec x₁ i = zVec x₂ i := by
      intro i
      have h := hmod i
      rw [hm0, zero_mul, sub_eq_zero] at h
      exact h
    have hS_eq : x₁.1 = x₂.1 := by
      apply Subtype.ext
      ext i
      rw [← hz_zero_iff x₁ i, ← hz_zero_iff x₂ i, hz_eq i, halpha]
    rcases x₁ with ⟨S₁, r₁⟩
    rcases x₂ with ⟨S₂, r₂⟩
    dsimp at hS_eq
    subst hS_eq
    congr 1
    apply Fin.ext
    dsimp [alphaVal] at halpha
    have hg_pos : (0 : ℝ) < ((S₁.1.gcd w : ℕ) : ℝ) := Nat.cast_pos.mpr (hsub_gcd_pos S₁.2)
    have hr_real : (r₁.val : ℝ) = (r₂.val : ℝ) := (div_left_inj' (ne_of_gt hg_pos)).mp halpha
    exact_mod_cast hr_real
  let proj : Idx → { u : Fin k → ZMod ℓ // bLin u = 0 } :=
    fun x => (kerEquiv.symm (fun i => (zVec x i : ZMod ℓ))).1
  have hcard_lt : Fintype.card { u : Fin k → ZMod ℓ // bLin u = 0 } < Fintype.card Idx := by
    rw [hcard_ker, hcard_idx]
    exact hsum
  obtain ⟨x₁, x₂, hne, hproj⟩ := Fintype.exists_ne_map_eq_of_card_lt proj hcard_lt
  let y₁ : Fin k → ZMod ℓ := fun i => (zVec x₁ i : ZMod ℓ)
  let y₂ : Fin k → ZMod ℓ := fun i => (zVec x₂ i : ZMod ℓ)
  let t_mod : ZMod ℓ := bLin y₁ - bLin y₂
  let m : ℤ := (t_mod.val : ℤ)
  have hdvd : ∀ i : Fin k, (ℓ : ℤ) ∣ (zVec x₁ i - zVec x₂ i - m * (w i : ℤ)) := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h_eq_i := congr_fun (congr_arg Subtype.val hproj) i
    dsimp [proj, kerEquiv] at h_eq_i
    have ht_cast : (m : ZMod ℓ) = t_mod := by
      dsimp [m]
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    push_cast
    rw [ht_cast]
    dsimp [t_mod, y₁, y₂]
    linear_combination h_eq_i
  let q : Fin k → ℤ := fun i => Classical.choose (hdvd i)
  have hq_spec : ∀ i : Fin k, zVec x₁ i - zVec x₂ i - m * (w i : ℤ) = (ℓ : ℤ) * q i :=
    fun i => Classical.choose_spec (hdvd i)
  have hnot_prop : ¬ ∃ γ : ℝ, ∀ i : Fin k, (q i : ℝ) = γ * (w i : ℝ) := by
    rintro ⟨γ, hγ⟩
    have hreal : ∀ i : Fin k,
        (zVec x₁ i : ℝ) - (zVec x₂ i : ℝ) = ((m : ℝ) + (ℓ : ℝ) * γ) * (w i : ℝ) := by
      intro i
      have hi : (zVec x₁ i : ℝ) - (zVec x₂ i : ℝ) - (m : ℝ) * (w i : ℝ) =
          (ℓ : ℝ) * (q i : ℝ) := by exact_mod_cast hq_spec i
      rw [hγ i] at hi
      linarith
    let m' : ℤ := ∑ i : Fin k, c i * (zVec x₁ i - zVec x₂ i)
    have hm'_real : (m' : ℝ) = (m : ℝ) + (ℓ : ℝ) * γ := by
      dsimp [m']
      push_cast
      have hsum_eq : ∑ i : Fin k, (c i : ℝ) * ((zVec x₁ i : ℝ) - (zVec x₂ i : ℝ)) =
          ((m : ℝ) + (ℓ : ℝ) * γ) * ∑ i : Fin k, (c i : ℝ) * (w i : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hreal i]
        ring
      have hc_real : ∑ i : Fin k, (c i : ℝ) * (w i : ℝ) = 1 := by exact_mod_cast hc
      rw [hsum_eq, hc_real, mul_one]
    have hmod_m' : ∀ i : Fin k, zVec x₁ i - zVec x₂ i = m' * (w i : ℤ) := by
      intro i
      have hi := hreal i
      rw [← hm'_real] at hi
      exact_mod_cast hi
    exact hne (hz_inj hmod_m')
  let β : ℝ := (alphaVal x₁ - alphaVal x₂ + (m : ℝ)) / (ℓ : ℝ)
  refine ⟨q, β, hnot_prop, ?_⟩
  intro i
  have hℓ_real_pos : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr hℓ_pos
  have hℓ_real_eq : (ℓ : ℝ) = ((k : ℝ) * ((k : ℝ) + 1)) / 2 := by
    have h2 : (2 : ℝ) * (ℓ : ℝ) = (k : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast hℓ_two
    linarith
  have hlin : (ℓ : ℝ) * ((q i : ℝ) + β * (w i : ℝ)) =
      ((zVec x₁ i : ℝ) + alphaVal x₁ * (w i : ℝ)) -
      ((zVec x₂ i : ℝ) + alphaVal x₂ * (w i : ℝ)) := by
    have hi : (zVec x₁ i : ℝ) - (zVec x₂ i : ℝ) - (m : ℝ) * (w i : ℝ) =
        (ℓ : ℝ) * (q i : ℝ) := by exact_mod_cast hq_spec i
    dsimp [β]
    field_simp [ne_of_gt hℓ_real_pos]
    linarith
  obtain ⟨hz1_0, hz1_1⟩ := hz_Icc x₁ i
  obtain ⟨hz2_0, hz2_1⟩ := hz_Icc x₂ i
  have habs_mul : |(ℓ : ℝ) * ((q i : ℝ) + β * (w i : ℝ))| ≤ 1 := by
    rw [hlin, abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_of_pos hℓ_real_pos] at habs_mul
  have hk_pos : (0 : ℝ) < (k : ℝ) * ((k : ℝ) + 1) := by positivity
  rw [hℓ_real_eq] at habs_mul
  rw [le_div_iff₀ hk_pos]
  linarith

private lemma exists_merged_speeds {k : ℕ} (hk : 3 ≤ k) {w : Fin k → ℕ}
    (hw : ∀ i, 0 < w i) (hmono : StrictMono w) {q : Fin k → ℤ}
    (hnot_prop : ¬ ∃ γ : ℝ, ∀ i : Fin k, (q i : ℝ) = γ * (w i : ℝ)) :
    ∃ (Δw Δq : ℤ) (m : ℕ) (u : Fin m → ℕ),
      1 ≤ m ∧ m < k ∧ (∀ j : Fin m, 0 < u j) ∧ StrictMono u ∧
      ∀ i : Fin k, ∃ j : Fin m, |q i * Δw - (w i : ℤ) * Δq| = (u j : ℤ) := by
  have huniv_ne : (Finset.univ : Finset (Fin k)).Nonempty := by
    refine ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  let ratio : Fin k → ℝ := fun i => (q i : ℝ) / (w i : ℝ)
  obtain ⟨i_min, _, hmin⟩ := Finset.exists_min_image Finset.univ ratio huniv_ne
  obtain ⟨i_max, _, hmax⟩ := Finset.exists_max_image Finset.univ ratio huniv_ne
  have hlt_ratio : ratio i_min < ratio i_max := by
    rcases lt_or_eq_of_le (hmin i_max (Finset.mem_univ _)) with hlt | heq
    · exact hlt
    · exfalso
      apply hnot_prop
      refine ⟨ratio i_min, fun i => ?_⟩
      have hi_ge := hmin i (Finset.mem_univ _)
      have hi_le := hmax i (Finset.mem_univ _)
      have hi_eq : ratio i = ratio i_min := by linarith
      dsimp [ratio] at hi_eq
      have hwi : (0 : ℝ) < (w i : ℝ) := Nat.cast_pos.mpr (hw i)
      exact (div_eq_iff (ne_of_gt hwi)).mp hi_eq
  have hne_idx : i_min ≠ i_max := fun h => by rw [h] at hlt_ratio; exact lt_irrefl _ hlt_ratio
  let a : Fin k := if i_min < i_max then i_min else i_max
  let b : Fin k := if i_min < i_max then i_max else i_min
  have hab_lt : a < b := by
    dsimp [a, b]
    split_ifs with h
    · exact h
    · exact lt_of_le_of_ne (le_of_not_gt h) hne_idx.symm
  have hab_ne : a ≠ b := ne_of_lt hab_lt
  have hwa_lt_wb : w a < w b := hmono hab_lt
  let Δw : ℤ := (w b : ℤ) - (w a : ℤ)
  let Δq : ℤ := q b - q a
  have hΔw_pos : (0 : ℝ) < (Δw : ℝ) := by
    dsimp [Δw]
    push_cast
    exact sub_pos.mpr (Nat.cast_lt.mpr hwa_lt_wb)
  have hdet_ne : ∀ i : Fin k, q i * Δw - (w i : ℤ) * Δq ≠ 0 := by
    intro i
    have hwi_pos : (0 : ℝ) < (w i : ℝ) := Nat.cast_pos.mpr (hw i)
    have hwa_pos : (0 : ℝ) < (w a : ℝ) := Nat.cast_pos.mpr (hw a)
    have hwb_pos : (0 : ℝ) < (w b : ℝ) := Nat.cast_pos.mpr (hw b)
    have hreal_ne : (q i : ℝ) * (Δw : ℝ) - (w i : ℝ) * (Δq : ℝ) ≠ 0 := by
      by_cases hcond : i_min < i_max
      · have ha_eq : a = i_min := if_pos hcond
        have hb_eq : b = i_max := if_pos hcond
        have hi_le : ratio i ≤ ratio b := by rw [hb_eq]; exact hmax i (Finset.mem_univ _)
        have ha_lt_b : ratio a < ratio b := by rw [ha_eq, hb_eq]; exact hlt_ratio
        dsimp [ratio] at hi_le ha_lt_b
        rw [div_lt_div_iff₀ hwa_pos hwb_pos] at ha_lt_b
        rw [div_le_div_iff₀ hwi_pos hwb_pos] at hi_le
        have h1 : (q i : ℝ) * (w b : ℝ) ≤ (q b : ℝ) * (w i : ℝ) := hi_le
        have h2 : (q a : ℝ) * (w b : ℝ) < (q b : ℝ) * (w a : ℝ) := ha_lt_b
        have hΔw_eq : (Δw : ℝ) = (w b : ℝ) - (w a : ℝ) := by dsimp [Δw]; push_cast; rfl
        have hΔq_eq : (Δq : ℝ) = (q b : ℝ) - (q a : ℝ) := by dsimp [Δq]; push_cast; rfl
        rw [hΔw_eq, hΔq_eq]
        have hprod : ((q i : ℝ) * ((w b : ℝ) - (w a : ℝ)) -
            (w i : ℝ) * ((q b : ℝ) - (q a : ℝ))) * (w b : ℝ) < 0 := by
          calc
            ((q i : ℝ) * ((w b : ℝ) - (w a : ℝ)) -
                (w i : ℝ) * ((q b : ℝ) - (q a : ℝ))) * (w b : ℝ)
              = ((q i : ℝ) * (w b : ℝ) - (q b : ℝ) * (w i : ℝ)) * ((w b : ℝ) - (w a : ℝ)) +
                (w i : ℝ) * ((q a : ℝ) * (w b : ℝ) - (q b : ℝ) * (w a : ℝ)) := by ring
            _ < 0 := by
              have hterm1 : ((q i : ℝ) * (w b : ℝ) - (q b : ℝ) * (w i : ℝ)) *
                  ((w b : ℝ) - (w a : ℝ)) ≤ 0 :=
                mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
              have hterm2 : (w i : ℝ) * ((q a : ℝ) * (w b : ℝ) - (q b : ℝ) * (w a : ℝ)) < 0 :=
                mul_neg_of_pos_of_neg hwi_pos (by linarith)
              linarith
        intro hzero
        rw [hzero, zero_mul] at hprod
        exact lt_irrefl 0 hprod
      · have ha_eq : a = i_max := if_neg hcond
        have hb_eq : b = i_min := if_neg hcond
        have hi_ge : ratio b ≤ ratio i := by rw [hb_eq]; exact hmin i (Finset.mem_univ _)
        have hb_lt_a : ratio b < ratio a := by rw [ha_eq, hb_eq]; exact hlt_ratio
        dsimp [ratio] at hi_ge hb_lt_a
        rw [div_lt_div_iff₀ hwb_pos hwa_pos] at hb_lt_a
        rw [div_le_div_iff₀ hwb_pos hwi_pos] at hi_ge
        have h1 : (q b : ℝ) * (w i : ℝ) ≤ (q i : ℝ) * (w b : ℝ) := hi_ge
        have h2 : (q b : ℝ) * (w a : ℝ) < (q a : ℝ) * (w b : ℝ) := hb_lt_a
        have hΔw_eq : (Δw : ℝ) = (w b : ℝ) - (w a : ℝ) := by dsimp [Δw]; push_cast; rfl
        have hΔq_eq : (Δq : ℝ) = (q b : ℝ) - (q a : ℝ) := by dsimp [Δq]; push_cast; rfl
        rw [hΔw_eq, hΔq_eq]
        have hprod : 0 < ((q i : ℝ) * ((w b : ℝ) - (w a : ℝ)) -
            (w i : ℝ) * ((q b : ℝ) - (q a : ℝ))) * (w b : ℝ) := by
          calc
            0 < ((q i : ℝ) * (w b : ℝ) - (q b : ℝ) * (w i : ℝ)) * ((w b : ℝ) - (w a : ℝ)) +
                (w i : ℝ) * ((q a : ℝ) * (w b : ℝ) - (q b : ℝ) * (w a : ℝ)) := by
              have hterm1 : 0 ≤ ((q i : ℝ) * (w b : ℝ) - (q b : ℝ) * (w i : ℝ)) *
                  ((w b : ℝ) - (w a : ℝ)) :=
                mul_nonneg (by linarith) (by linarith)
              have hterm2 : 0 < (w i : ℝ) * ((q a : ℝ) * (w b : ℝ) - (q b : ℝ) * (w a : ℝ)) :=
                mul_pos hwi_pos (by linarith)
              linarith
            _ = ((q i : ℝ) * ((w b : ℝ) - (w a : ℝ)) -
                (w i : ℝ) * ((q b : ℝ) - (q a : ℝ))) * (w b : ℝ) := by ring
        intro hzero
        rw [hzero, zero_mul] at hprod
        exact lt_irrefl 0 hprod
    intro hzero
    apply hreal_ne
    exact_mod_cast hzero
  have hdet_ab : q a * Δw - (w a : ℤ) * Δq = q b * Δw - (w b : ℤ) * Δq := by
    dsimp [Δw, Δq]
    ring
  let D : Fin k → ℕ := fun i => (q i * Δw - (w i : ℤ) * Δq).natAbs
  let U : Finset ℕ := (Finset.univ.erase b).image D
  have ha_mem_erase : a ∈ Finset.univ.erase b :=
    Finset.mem_erase.mpr ⟨hab_ne, Finset.mem_univ a⟩
  have hU_nonempty : U.Nonempty := ⟨D a, Finset.mem_image_of_mem D ha_mem_erase⟩
  let m : ℕ := U.card
  have hm_ge : 1 ≤ m := Finset.card_pos.mpr hU_nonempty
  have hm_lt : m < k := by
    calc
      m ≤ (Finset.univ.erase b).card := Finset.card_image_le
      _ = k - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_fin]
      _ < k := by omega
  let emb := U.orderEmbOfFin rfl
  let u : Fin m → ℕ := fun j => emb j
  have hu_mono : StrictMono u := emb.strictMono
  have hu_pos : ∀ j : Fin m, 0 < u j := by
    intro j
    have hj_mem : u j ∈ U := Finset.orderEmbOfFin_mem U rfl j
    obtain ⟨i, _, hi_eq⟩ := Finset.mem_image.mp hj_mem
    rw [← hi_eq]
    exact Int.natAbs_pos.mpr (hdet_ne i)
  refine ⟨Δw, Δq, m, u, hm_ge, hm_lt, hu_pos, hu_mono, ?_⟩
  intro i
  have hDi_mem : D i ∈ U := by
    by_cases hib : i = b
    · subst hib
      have hDa_eq : D b = D a := by
        dsimp [D]
        rw [hdet_ab]
      rw [hDa_eq]
      exact Finset.mem_image_of_mem D ha_mem_erase
    · exact Finset.mem_image_of_mem D (Finset.mem_erase.mpr ⟨hib, Finset.mem_univ i⟩)
  have hDi_range : D i ∈ Set.range emb := by
    rw [Finset.range_orderEmbOfFin]
    exact hDi_mem
  obtain ⟨j, hj⟩ := hDi_range
  refine ⟨j, ?_⟩
  have hcast : ((D i : ℕ) : ℤ) = |q i * Δw - (w i : ℤ) * Δq| := Int.natCast_natAbs _
  rw [← hcast, ← hj]

private lemma mss_gcd_sum_reduction (k : ℕ) (hk : 3 ≤ k) (w : Fin k → ℕ)
    (hw : ∀ i : Fin k, 0 < w i) (hmono : StrictMono w) (hgcd : Finset.univ.gcd w = 1)
    (hsum : (Nat.choose (k + 1) 2) ^ (k - 1) <
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅, S.gcd w)
    (h_smaller : ∀ (m : ℕ), 1 ≤ m → m < k → ∀ (u : Fin m → ℕ),
      (∀ i : Fin m, 0 < u i) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  obtain ⟨q, β, hnot_prop, hshort⟩ := exists_short_nonproportional_vec hk hw hgcd hsum
  obtain ⟨Δw, Δq, m, u, hm_ge, hm_lt, hu_pos, hu_mono, hu_cover⟩ :=
    exists_merged_speeds hk hw hmono hnot_prop
  obtain ⟨τ, hτ_nonneg, hτ⟩ := h_smaller m hm_ge hm_lt u hu_pos hu_mono
  let s : ℝ := τ * (Δw : ℝ)
  let t₀ : ℝ := -τ * (Δq : ℝ)
  let sqReal : Fin k → ℝ := fun i => s * (q i : ℝ) + t₀ * (w i : ℝ)
  have hdist_sq : ∀ i : Fin k,
      dist ((sqReal i : ℝ) : UnitAddCircle) 0 ≥ 1 / (k : ℝ) := by
    intro i
    obtain ⟨j, hj⟩ := hu_cover i
    have hj_real : |(q i : ℝ) * (Δw : ℝ) - (w i : ℝ) * (Δq : ℝ)| = (u j : ℝ) := by
      exact_mod_cast hj
    have hexpr : sqReal i = τ * ((q i : ℝ) * (Δw : ℝ) - (w i : ℝ) * (Δq : ℝ)) := by
      dsimp [sqReal, s, t₀]
      ring
    have habs_tau : |τ * ((q i : ℝ) * (Δw : ℝ) - (w i : ℝ) * (Δq : ℝ))| = τ * (u j : ℝ) := by
      rw [abs_mul, abs_of_nonneg hτ_nonneg, hj_real]
    rw [hexpr, ← unitAddCircle_dist_abs_single, habs_tau]
    have hm_le_k : ((m + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hm_lt
    have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    calc
      dist ((τ * (u j : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := hτ j
      _ ≥ 1 / (k : ℝ) := one_div_le_one_div_of_le hm_pos hm_le_k
  let z_s : ℤ := ⌊s + 1 / 2⌋
  let θ : ℝ := (z_s : ℝ) - s
  have hθ_abs : |θ| ≤ 1 / 2 := by
    dsimp [θ, z_s]
    rw [abs_le]
    have h1 := Int.sub_one_lt_floor (s + 1 / 2)
    have h2 := Int.floor_le (s + 1 / 2)
    constructor <;> linarith
  let t₁ : ℝ := t₀ + θ * β
  let t : ℝ := |t₁|
  refine ⟨t, abs_nonneg t₁, ?_⟩
  intro i
  have ht_abs : dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 =
      dist ((t₁ * (w i : ℝ) : ℝ) : UnitAddCircle) 0 := by
    dsimp [t]
    have hw_abs : |(w i : ℝ)| = (w i : ℝ) := abs_of_pos (Nat.cast_pos.mpr (hw i))
    have hmul : |t₁| * (w i : ℝ) = |t₁ * (w i : ℝ)| := by
      rw [abs_mul, hw_abs]
    rw [hmul, unitAddCircle_dist_abs_single]
  rw [ht_abs]
  let yReal : ℝ := t₁ * (w i : ℝ)
  let errReal : ℝ := -θ * ((q i : ℝ) + β * (w i : ℝ))
  let X : UnitAddCircle := (sqReal i : UnitAddCircle)
  let Y : UnitAddCircle := (yReal : UnitAddCircle)
  have hdiff_eq : X - Y = (errReal : UnitAddCircle) := by
    change (sqReal i : UnitAddCircle) - (yReal : UnitAddCircle) = (errReal : UnitAddCircle)
    rw [← QuotientAddGroup.mk_sub]
    have hring : sqReal i - yReal = (((z_s * q i : ℤ) : ℝ)) + errReal := by
      dsimp [sqReal, yReal, errReal, t₁, θ]
      push_cast
      ring
    rw [hring, QuotientAddGroup.mk_add, unitAddCircle_int_cast_eq_zero, zero_add]
  have herr_le : |errReal| ≤ 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
    dsimp [errReal]
    calc
      |-θ * ((q i : ℝ) + β * (w i : ℝ))| = |θ| * |(q i : ℝ) + β * (w i : ℝ)| := by
        rw [abs_mul, abs_neg]
      _ ≤ (1 / 2) * (2 / ((k : ℝ) * ((k : ℝ) + 1))) :=
        mul_le_mul hθ_abs (hshort i) (abs_nonneg _) (by norm_num)
      _ = 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by ring
  have herr_lt_half : |errReal| < 1 / 2 := by
    have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk_prod : (12 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1) := by nlinarith
    have hfrac_lt : 1 / ((k : ℝ) * ((k : ℝ) + 1)) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    exact lt_of_le_of_lt herr_le hfrac_lt
  have hdist_XY : dist X Y ≤ 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
    rw [dist_eq_norm, hdiff_eq, ← dist_zero_right, unitAddCircle_dist_eq_abs_of_lt_half herr_lt_half]
    exact herr_le
  have htri : dist X 0 ≤ dist X Y + dist Y 0 := dist_triangle X Y 0
  have hX0 : 1 / (k : ℝ) ≤ dist X 0 := hdist_sq i
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hfrac : 1 / (k : ℝ) - 1 / ((k : ℝ) * ((k : ℝ) + 1)) = 1 / (((k + 1 : ℕ) : ℝ)) := by
    push_cast
    field_simp [ne_of_gt hk_pos, ne_of_gt hk1_pos]
    ring
  linarith

/- ### Module 5: Unified Sieve Bootstrap for k = 1..7 -/

private lemma lrc_nat_le_four :
    ∀ (m : ℕ), 1 ≤ m → m ≤ 4 → ∀ (u : Fin m → ℕ),
      (∀ i : Fin m, 0 < u i) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  intro m hm1 hm4 u hu_pos hu_mono
  rcases eq_or_ne m 1 with rfl | hm_ne1
  · exact lrc_pos_one (fun i => (u i : ℝ)) (fun i => Nat.cast_pos.mpr (hu_pos i))
  rcases eq_or_ne m 2 with rfl | hm_ne2
  · exact lrc_pos_two (fun i => (u i : ℝ))
      (fun i => Nat.cast_pos.mpr (hu_pos i)) (fun i j hij => Nat.cast_lt.mpr (hu_mono hij))
  rcases eq_or_ne m 3 with rfl | hm_ne3
  · exact lrc_pos_three (fun i => (u i : ℝ))
      (fun i => Nat.cast_pos.mpr (hu_pos i)) (fun i j hij => Nat.cast_lt.mpr (hu_mono hij))
  have hm_eq4 : m = 4 := by omega
  subst hm_eq4
  refine lrc_nat_gcd_reduction 4 (by decide) u hu_pos hu_mono ?_
  intro w hw_pos _ hw_gcd
  by_cases hdvd5 : ∃ i : Fin 4, 5 ∣ w i
  · exact lrc_nat_four w hw_pos hw_gcd hdvd5
  · exact lrc_small_divisor_sieve (k := 4) (j := 5) (by decide) (by decide) w
      (fun i hi => hdvd5 ⟨i, hi⟩)

private lemma lrc_sieved_prim_step {k : ℕ} (hk5 : 5 ≤ k)
    (h_smaller : ∀ (m : ℕ), 1 ≤ m → m < k → ∀ (u : Fin m → ℕ),
      (∀ i : Fin m, 0 < u i) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ))
    (h_core : ∀ (w : Fin k → ℕ),
      (∀ i : Fin k, 0 < w i) →
      StrictMono w →
      Finset.univ.gcd w = 1 →
      (∀ i₀ : Fin k, (Finset.univ.erase i₀).gcd w = 1) →
      (∀ j : ℕ, 2 ≤ j → j ≤ k + 1 → ∃ i : Fin k, j ∣ w i) →
      (∀ q : ℕ, Nat.Prime q → 3 ≤ q → (Finset.univ.filter (fun i : Fin k => q ∣ w i)).card ≤ k - 3) →
      (7 ≤ k → ∀ q : ℕ, Nat.Prime q → 7 ≤ q →
        (Finset.univ.filter (fun i : Fin k => q ∣ w i)).card ≤ k - 4) →
      (∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧ (k - 1) * w j < 2 * k * w i) →
      (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅, S.gcd w) ≤
        (Nat.choose (k + 1) 2) ^ (k - 1) →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)) :
    ∀ (w : Fin k → ℕ), (∀ i : Fin k, 0 < w i) → StrictMono w → Finset.univ.gcd w = 1 →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  intro w hw_pos hw_mono hw_gcd
  rcases lt_or_ge ((Nat.choose (k + 1) 2) ^ (k - 1))
      (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅, S.gcd w) with hsum_gt | hsum_le
  · exact mss_gcd_sum_reduction k (by omega) w hw_pos hw_mono hw_gcd hsum_gt h_smaller
  by_cases h_sub : ∀ i₀ : Fin k, (Finset.univ.erase i₀).gcd w = 1
  · by_cases h_sdiv : ∀ j : ℕ, 2 ≤ j → j ≤ k + 1 → ∃ i : Fin k, j ∣ w i
    · by_cases h_odd : ∀ q : ℕ, Nat.Prime q → 3 ≤ q →
          (Finset.univ.filter (fun i : Fin k => q ∣ w i)).card ≤ k - 3
      · by_cases h_p7 : 7 ≤ k → ∀ q : ℕ, Nat.Prime q → 7 ≤ q →
            (Finset.univ.filter (fun i : Fin k => q ∣ w i)).card ≤ k - 4
        · by_cases hlac : ∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧
              (k - 1) * w j < 2 * k * w i
          · exact h_core w hw_pos hw_mono hw_gcd h_sub h_sdiv h_odd h_p7 hlac hsum_le
          · exact lrc_lacunary_nat k (by omega) w hw_pos hw_mono hlac
        · simp only [not_forall, not_le] at h_p7
          obtain ⟨hk7, q, hq, hq7, hmult⟩ := h_p7
          exact lrc_nat_prime_multiplicity_sieve (m₀ := k - 3) (by omega) hq (by omega)
            (prime_ge_seven_cap_le hk7 hq hq7) w hw_pos hw_mono hw_gcd (by omega) h_smaller
      · simp only [not_forall, not_le] at h_odd
        obtain ⟨q, hq, hq3, hmult⟩ := h_odd
        exact lrc_nat_prime_multiplicity_sieve (m₀ := k - 2) (by omega) hq (by omega)
          (odd_prime_cap_le hk5 hq hq3) w hw_pos hw_mono hw_gcd (by omega) h_smaller
    · simp only [not_forall, not_exists] at h_sdiv
      obtain ⟨j, hj2, hjk, hndvd⟩ := h_sdiv
      exact lrc_small_divisor_sieve hj2 hjk w hndvd
  · simp only [not_forall] at h_sub
    obtain ⟨i₀, hi₀⟩ := h_sub
    exact lrc_nat_one_exception_sieve k (by omega) w hw_pos hw_mono hw_gcd i₀ hi₀
      (fun u hu_pos hu_mono => h_smaller (k - 1) (by omega) (by omega) u hu_pos hu_mono)

end

end ReductionProofs

theorem main : H1 → H2 → H3 → OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1.H2 := by
  intro h1 h2 h3
  have h_le5 : ∀ (m : ℕ), 1 ≤ m → m ≤ 5 → ∀ (u : Fin m → ℕ),
      (∀ i : Fin m, 0 < u i) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
    intro m hm1 hm5 u hu_pos hu_mono
    rcases lt_or_eq_of_le hm5 with hlt | rfl
    · exact lrc_nat_le_four m hm1 (by omega) u hu_pos hu_mono
    · refine lrc_nat_gcd_reduction 5 (by decide) u hu_pos hu_mono ?_
      exact lrc_sieved_prim_step (by decide)
        (fun m' hm'1 hm'lt u' hu'_pos hu'_mono => lrc_nat_le_four m' hm'1 (by omega) u' hu'_pos hu'_mono)
        (fun w hw_pos hw_mono hw_gcd h_sub h_sdiv h_odd _ hlac hsum_le =>
          h1 w hw_pos hw_mono hw_gcd h_sub h_sdiv h_odd hlac hsum_le)
  have h_le6 : ∀ (m : ℕ), 1 ≤ m → m ≤ 6 → ∀ (u : Fin m → ℕ),
      (∀ i : Fin m, 0 < u i) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
    intro m hm1 hm6 u hu_pos hu_mono
    rcases lt_or_eq_of_le hm6 with hlt | rfl
    · exact h_le5 m hm1 (by omega) u hu_pos hu_mono
    · refine lrc_nat_gcd_reduction 6 (by decide) u hu_pos hu_mono ?_
      refine lrc_sieved_prim_step (by decide)
        (fun m' hm'1 hm'lt u' hu'_pos hu'_mono => h_le5 m' hm'1 (by omega) u' hu'_pos hu'_mono) ?_
      intro w hw_pos hw_mono hw_gcd h_sub h_sdiv h_odd _ hlac hsum_le
      have hc7_le3 : (Finset.univ.filter (fun i : Fin 6 => 7 ∣ w i)).card ≤ 3 :=
        h_odd 7 (by decide) (by decide)
      rcases lt_or_eq_of_le hc7_le3 with hc7_lt3 | hc7_eq3
      · exact h2 w hw_pos hw_mono hw_gcd h_sub h_sdiv h_odd (by omega) hlac hsum_le
      · exact lrc_six_three_mult_seven w hw_pos (h_sdiv 7 (by decide) (by decide)) hc7_eq3
  have h_le7 : ∀ (m : ℕ), 1 ≤ m → m ≤ 7 → ∀ (u : Fin m → ℕ),
      (∀ i : Fin m, 0 < u i) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
    intro m hm1 hm7 u hu_pos hu_mono
    rcases lt_or_eq_of_le hm7 with hlt | rfl
    · exact h_le6 m hm1 (by omega) u hu_pos hu_mono
    · refine lrc_nat_gcd_reduction 7 (by decide) u hu_pos hu_mono ?_
      exact lrc_sieved_prim_step (by decide)
        (fun m' hm'1 hm'lt u' hu'_pos hu'_mono => h_le6 m' hm'1 (by omega) u' hu'_pos hu'_mono)
        (fun w hw_pos hw_mono hw_gcd h_sub h_sdiv h_odd h_p7 hlac hsum_le =>
          h3 w hw_pos hw_mono hw_gcd h_sub h_sdiv h_odd (h_p7 le_rfl) hlac hsum_le)
  intro k hk3 hk7 w hw_pos hw_mono _ _ _
  exact h_le7 k (by omega) hk7 w hw_pos hw_mono

end OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1_H2_R1
