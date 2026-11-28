import FormalConjectures.Wikipedia.LonelyRunnerConjecture
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
Reduction `LonelyRunnerConjecture.lonely_runner_conjecture.R2` of the Lonely Runner Conjecture.

Unconditionally proved in-file:
1. Stationary-frame and absolute-value collision strong induction (`n = 0, 1` base cases and
   reduction to `k` strictly increasing positive real speeds).
2. Exact unconditional proofs for all `n ≤ 4` runners (`k = 1, 2, 3`, including the Betke-Wills
   1972 four-runner theorem for arbitrary real speeds).
3. General lacunary nested-interval theorem for all `k ≥ 4`.
4. Full real-to-integer velocity reduction for all `k ≥ 4` (Bienia-Goddyn-Gvozdjak-Sebo-Tarsi
   1998; Bohman-Holzman-Kleitman 2001), proved via positive-time multivariate Fourier/Kronecker
   density on `UnitAddTorus` and rational mediant sign-collision.
5. Primitive common-divisor scaling, `(k + 1)`-divisibility sieve, and Rosenfeld's `(k - 1)`-subset
   coprimality sieve (`∀ i₀, (Finset.univ.erase i₀).gcd w = 1`).

Remaining three discrete integer pillars (`k ≥ 4`, i.e. `n ≥ 5` total runners):
- `H1`: Verified finite-runner integer regimes `4 ≤ k ≤ 9` (`5 ≤ n ≤ 10` runners: Cusick-Pomerance
  1984, Bohman-Holzman-Kleitman 2001, Barajas-Serra 2008, Rosenfeld 2025-2026, Trakulthongchai 2026).
- `H2`: Malikiosis-Santos-Schymura (2025) zonotopal GCD-sum finite-checking reduction for `k ≥ 10`
  via `∑_{∅ ≠ S ⊆ Fin k} S.gcd w ≤ (Nat.choose (k + 1) 2) ^ (k - 1)`.
- `H3`: Open bounded-zonotope integer frontier for `k ≥ 10` (`n ≥ 11` total runners).
-/

-- Reduction LonelyRunnerConjecture.lonely_runner_conjecture.R2 of Lonely runner conjecture
-- Credit: @paynebrowning

namespace OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R2

-- Pillar 1: Verified integer regimes for 5 to 10 total runners (4 <= k <= 9 moving runners),
-- restricted to primitive, (k - 1)-coprime, non-lacunary tuples with a multiple of k + 1.
def H1 : Prop :=
  ∀ (k : ℕ), 4 ≤ k → k ≤ 9 → ∀ (w : Fin k → ℕ),
    (∀ i : Fin k, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∀ i₀ : Fin k, (Finset.univ.erase i₀).gcd w = 1) →
    (∃ i : Fin k, (k + 1) ∣ w i) →
    (∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧ (k - 1) * w j < 2 * k * w i) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)

-- Pillar 2 (Malikiosis-Santos-Schymura 2025): Zonotopal GCD-sum finite-checking reduction
-- for k >= 10, reducing tuples with subset-GCD sum exceeding C(k+1, 2)^(k-1) to smaller runner
-- counts and bounded-zonotope tuples.
def H2 : Prop :=
  ∀ (k : ℕ), 10 ≤ k → ∀ (w : Fin k → ℕ),
    (∀ i : Fin k, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∀ i₀ : Fin k, (Finset.univ.erase i₀).gcd w = 1) →
    (∃ i : Fin k, (k + 1) ∣ w i) →
    (∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧ (k - 1) * w j < 2 * k * w i) →
    (Nat.choose (k + 1) 2) ^ (k - 1) <
      (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅, S.gcd w) →
    (∀ (m : ℕ), 1 ≤ m → m < k → ∀ (u : Fin m → ℕ),
      (∀ i : Fin m, 0 < u i) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ)) →
    (∀ (u : Fin k → ℕ),
      (∀ i : Fin k, 0 < u i) → StrictMono u → Finset.univ.gcd u = 1 →
      (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅, S.gcd u) ≤
        (Nat.choose (k + 1) 2) ^ (k - 1) →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin k, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)

-- Pillar 3: Open bounded-zonotope integer frontier for 11 or more total runners (k >= 10),
-- restricted to primitive, (k - 1)-coprime, non-lacunary tuples with a multiple of k + 1
-- and subset-GCD sum at most C(k+1, 2)^(k-1).
def H3 : Prop :=
  ∀ (k : ℕ), 10 ≤ k → ∀ (w : Fin k → ℕ),
    (∀ i : Fin k, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∀ i₀ : Fin k, (Finset.univ.erase i₀).gcd w = 1) →
    (∃ i : Fin k, (k + 1) ∣ w i) →
    (∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧ (k - 1) * w j < 2 * k * w i) →
    (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅, S.gcd w) ≤
      (Nat.choose (k + 1) 2) ^ (k - 1) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)

section ReductionProofs

noncomputable section

open scoped ComplexConjugate
open Set Submodule MeasureTheory UnitAddTorus

private lemma unitAddCircle_dist_eq (a b : ℝ) :
    dist (a : UnitAddCircle) (b : UnitAddCircle) = dist ((a - b : ℝ) : UnitAddCircle) 0 := by
  rw [dist_eq_norm, dist_zero_right, ← QuotientAddGroup.mk_sub]

private lemma unitAddCircle_dist_mul_sub (t a b : ℝ) :
    dist (t * a : UnitAddCircle) (t * b : UnitAddCircle) =
      dist ((t * (b - a) : ℝ) : UnitAddCircle) 0 := by
  rw [dist_comm, unitAddCircle_dist_eq]
  congr 2
  ring

private lemma unitAddCircle_dist_neg (x : ℝ) :
    dist ((-x : ℝ) : UnitAddCircle) 0 = dist (x : UnitAddCircle) 0 := by
  rw [dist_zero_right, dist_zero_right, QuotientAddGroup.mk_neg, norm_neg]

private lemma unitAddCircle_dist_abs (t x : ℝ) :
    dist ((t * |x| : ℝ) : UnitAddCircle) 0 = dist ((t * x : ℝ) : UnitAddCircle) 0 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, mul_neg, unitAddCircle_dist_neg]

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
    refine ⟨C / v 1, le_div_iff₀ hv1 |>.mpr (by linarith [ show (0 : ℝ) ≤ v 1 / (3 * v 0) by positivity ]), fun i => ?_⟩
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

-- Betke-Wills (1972) unconditional solution for 4 total runners (3 moving positive real speeds).
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
    · -- Interval I₂ = [5 / (4 * v 1), 7 / (4 * v 1)] has v 2 * length = v 2 / (2 * v 1) > 1/2.
      have hlen : 2 * (0 : ℝ) + 2 * (1 / 4 : ℝ) ≤
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
      · -- Explicit time t = 1 / (4 * v 0) places all three speeds in [1/4, 3/4].
        refine ⟨1 / (4 * v 0), by positivity, fun i => ?_⟩
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
        · -- Interval I₁ = [1 / (4 * v 0), 3 / (4 * v 1)] has v 2 * length ≥ 1/2.
          have hlen : 2 * (0 : ℝ) + 2 * (1 / 4 : ℝ) ≤
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
            · -- Explicit time t = 3 / (4 * v 1) ∈ I₁ gives t * v 2 ∈ [5/4, 7/4].
              refine ⟨3 / (4 * v 1), by positivity, fun i => ?_⟩
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
            · -- Explicit time t = 7 / (4 * v 2) ∈ I₁ (since v 2 < 7 * v 0).
              have hv2_lt7 : v 2 < 7 * v 0 := by nlinarith
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
          · -- Remaining regime (3 * v 0 < v 2, 3 * v 2 < 5 * v 1, 3 * v 1 < 7 * v 0):
            -- Explicit time t = 9 / (4 * v 2) places t * v 0 ∈ [1/4, 3/4], t * v 1 ∈ [5/4, 7/4], t * v 2 = 9/4.
            refine ⟨9 / (4 * v 2), by positivity, fun i => ?_⟩
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

private lemma lrc_reduction_to_pos_strictMono
    (h_pos : ∀ (k : ℕ), 4 ≤ k → ∀ (v : Fin k → ℝ),
      (∀ i : Fin k, 0 < v i) → StrictMono v →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin k, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)) :
    ∀ (n : ℕ) (speed : Fin n ↪ ℝ) (r : Fin n),
      ∃ t : ℝ, t ≥ 0 ∧ ∀ r2 : Fin n, r2 ≠ r →
        dist (t * speed r : UnitAddCircle) (t * speed r2) ≥ 1 / (n : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro speed r
    rcases eq_or_ne n 0 with rfl | hn0
    · exact Fin.elim0 r
    rcases eq_or_ne n 1 with rfl | hn1
    · refine ⟨0, le_rfl, fun r2 hr2 => absurd (Subsingleton.elim r2 r) hr2⟩
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
    let U : Finset (Fin (k + 1)) := Finset.univ.erase r
    have hU_card : U.card = k := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_fin]; omega
    let S : Finset ℝ := U.image (fun i => |speed i - speed r|)
    have hS_pos : ∀ x ∈ S, 0 < x := by
      intro x hx
      obtain ⟨i, hiU, rfl⟩ := Finset.mem_image.mp hx
      exact abs_pos.mpr (sub_ne_zero.mpr (speed.injective.ne (Finset.ne_of_mem_erase hiU)))
    have hS_le : S.card ≤ U.card := Finset.card_image_le
    rcases lt_or_eq_of_le hS_le with hlt_card | heq_card
    · have h0_not_mem : (0 : ℝ) ∉ S := fun h0 => (lt_irrefl (0 : ℝ)) (hS_pos 0 h0)
      let S0 : Finset ℝ := insert 0 S
      let m : ℕ := S0.card
      have hm_eq : m = S.card + 1 := Finset.card_insert_of_notMem h0_not_mem
      have hm_lt : m < k + 1 := by omega
      let emb : Fin m ↪ ℝ := (S0.orderEmbOfFin rfl).toEmbedding
      have h_range : Set.range emb = (S0 : Set ℝ) := Finset.range_orderEmbOfFin S0 rfl
      have h0_mem : (0 : ℝ) ∈ (S0 : Set ℝ) := Finset.mem_coe.mpr (Finset.mem_insert_self 0 S)
      obtain ⟨r0, hr0⟩ : ∃ r0 : Fin m, emb r0 = 0 := by rwa [← h_range] at h0_mem
      obtain ⟨t, ht0, ht_lonely⟩ := ih m hm_lt emb r0
      refine ⟨t, ht0, fun r2 hr2 => ?_⟩
      have hr2_U : r2 ∈ U := Finset.mem_erase.mpr ⟨hr2, Finset.mem_univ r2⟩
      have hx_S : |speed r2 - speed r| ∈ S := Finset.mem_image.mpr ⟨r2, hr2_U, rfl⟩
      have hx_pos : 0 < |speed r2 - speed r| := hS_pos _ hx_S
      have hx_S0 : |speed r2 - speed r| ∈ (S0 : Set ℝ) :=
        Finset.mem_coe.mpr (Finset.mem_insert_of_mem hx_S)
      obtain ⟨j, hj⟩ : ∃ j : Fin m, emb j = |speed r2 - speed r| := by rwa [← h_range] at hx_S0
      have hj_ne : j ≠ r0 := fun h_eq => by rw [h_eq, hr0] at hj; linarith
      have h_step := ht_lonely j hj_ne
      rw [hr0, mul_zero, hj] at h_step
      have h_zero_coe : ((0 : ℝ) : UnitAddCircle) = 0 := QuotientAddGroup.mk_zero _
      rw [h_zero_coe, dist_comm] at h_step
      rw [unitAddCircle_dist_mul_sub, ← unitAddCircle_dist_abs]
      have h_mn : 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 / (m : ℝ) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hm_lt.le)
      exact le_trans h_mn h_step
    · have hk_eq : S.card = k := heq_card.trans hU_card
      let emb := S.orderEmbOfFin hk_eq
      let v : Fin k → ℝ := fun i => emb i
      have hv_pos : ∀ i : Fin k, 0 < v i :=
        fun i => hS_pos (v i) (Finset.orderEmbOfFin_mem S hk_eq i)
      have hv_mono : StrictMono v := emb.strictMono
      have h_v_lonely : ∃ t : ℝ, t ≥ 0 ∧
          ∀ i : Fin k, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
        rcases eq_or_ne k 1 with rfl | hk_ne1
        · exact lrc_pos_one v hv_pos
        · rcases eq_or_ne k 2 with rfl | hk_ne2
          · exact lrc_pos_two v hv_pos hv_mono
          · rcases eq_or_ne k 3 with rfl | hk_ne3
            · exact lrc_pos_three v hv_pos hv_mono
            · exact h_pos k (by omega) v hv_pos hv_mono
      obtain ⟨t, ht0, ht_v⟩ := h_v_lonely
      refine ⟨t, ht0, fun r2 hr2 => ?_⟩
      have hr2_U : r2 ∈ U := Finset.mem_erase.mpr ⟨hr2, Finset.mem_univ r2⟩
      have hx_S : |speed r2 - speed r| ∈ (S : Set ℝ) :=
        Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨r2, hr2_U, rfl⟩)
      have h_range : Set.range v = (S : Set ℝ) := Finset.range_orderEmbOfFin S hk_eq
      obtain ⟨i, hi⟩ : ∃ i : Fin k, v i = |speed r2 - speed r| := by rwa [← h_range] at hx_S
      rw [unitAddCircle_dist_mul_sub, ← unitAddCircle_dist_abs, ← hi]
      exact ht_v i

private lemma exists_finset_of_mem_span_mFourier {d : ℕ}
    {P : C(UnitAddTorus (Fin d), ℂ)}
    (hP : P ∈ span ℂ (range (mFourier (d := Fin d)))) :
    ∃ (F : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
      0 ∈ F ∧ ∀ x : UnitAddTorus (Fin d), P x = ∑ n ∈ F, c n * mFourier n x := by
  classical
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hP
  · rintro _ ⟨n₀, rfl⟩
    refine ⟨insert 0 {n₀}, fun n => if n = n₀ then 1 else 0, Finset.mem_insert_self 0 {n₀}, fun x => ?_⟩
    rcases eq_or_ne n₀ 0 with rfl | hn0
    · simp
    · rw [Finset.sum_insert (Finset.notMem_singleton.mpr hn0.symm), Finset.sum_singleton]
      simp [hn0.symm]
  · refine ⟨{0}, fun _ => 0, Finset.mem_singleton_self 0, fun x => ?_⟩
    simp
  · rintro P₁ P₂ _ _ ⟨F₁, c₁, h0₁, h₁⟩ ⟨F₂, c₂, _, h₂⟩
    refine ⟨F₁ ∪ F₂, fun n => (if n ∈ F₁ then c₁ n else 0) + (if n ∈ F₂ then c₂ n else 0),
      Finset.mem_union_left F₂ h0₁, fun x => ?_⟩
    change P₁ x + P₂ x = _
    rw [h₁ x, h₂ x]
    simp_rw [add_mul, Finset.sum_add_distrib]
    congr 1
    · have heq1 : (∑ n ∈ F₁, c₁ n * mFourier n x) =
          ∑ n ∈ F₁, (if n ∈ F₁ then c₁ n else 0) * mFourier n x :=
        Finset.sum_congr rfl fun n hn => by simp [hn]
      rw [heq1]
      exact Finset.sum_subset (Finset.subset_union_left : F₁ ⊆ F₁ ∪ F₂) fun n _ hn1 => by simp [hn1]
    · have heq2 : (∑ n ∈ F₂, c₂ n * mFourier n x) =
          ∑ n ∈ F₂, (if n ∈ F₂ then c₂ n else 0) * mFourier n x :=
        Finset.sum_congr rfl fun n hn => by simp [hn]
      rw [heq2]
      exact Finset.sum_subset (Finset.subset_union_right : F₂ ⊆ F₁ ∪ F₂) fun n _ hn2 => by simp [hn2]
  · rintro a P₁ _ ⟨F₁, c₁, h0₁, h₁⟩
    refine ⟨F₁, fun n => a * c₁ n, h0₁, fun x => ?_⟩
    change a * P₁ x = _
    rw [h₁ x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring

private lemma exists_mFourier_approx {d : ℕ} (fC : C(UnitAddTorus (Fin d), ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (P : C(UnitAddTorus (Fin d), ℂ)) (F : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
      0 ∈ F ∧ ‖P - fC‖ < δ ∧
      ∀ x : UnitAddTorus (Fin d), P x = ∑ n ∈ F, c n * mFourier n x := by
  have h_top : (span ℂ (range (mFourier (d := Fin d)))).topologicalClosure = ⊤ :=
    UnitAddTorus.span_mFourier_closure_eq_top
  have hfC_mem : fC ∈ (span ℂ (range (mFourier (d := Fin d)))).topologicalClosure := by
    rw [h_top]; trivial
  have hfC_cl : (fC : C(UnitAddTorus (Fin d), ℂ)) ∈
      closure ((span ℂ (range (mFourier (d := Fin d)))) : Set C(UnitAddTorus (Fin d), ℂ)) := by
    rwa [← Submodule.topologicalClosure_coe]
  rw [Metric.mem_closure_iff] at hfC_cl
  obtain ⟨P, hP_mem, hP_dist⟩ := hfC_cl δ hδ
  have hP_norm : ‖P - fC‖ < δ := by rwa [dist_comm, dist_eq_norm] at hP_dist
  obtain ⟨F, c, h0F, hP_eval⟩ := exists_finset_of_mem_span_mFourier hP_mem
  exact ⟨P, F, c, h0F, hP_norm, hP_eval⟩

private lemma mFourier_eval_add {d : ℕ} (n : Fin d → ℤ) (x y : UnitAddTorus (Fin d)) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

private lemma mFourier_eval_nsmul {d : ℕ} (n : Fin d → ℤ) (m : ℕ) (x : UnitAddTorus (Fin d)) :
    mFourier n (m • x) = (mFourier n x) ^ m := by
  induction m with
  | zero => simp [mFourier]
  | succ m ih => rw [succ_nsmul, mFourier_eval_add, ih, pow_succ]

private lemma mFourier_ray_ne_one {d : ℕ} (e : Fin d → ℝ) (n : Fin d → ℤ)
    (tau : ℝ) (hpos : 0 < |tau * ∑ j : Fin d, (n j : ℝ) * e j|)
    (hlt : |tau * ∑ j : Fin d, (n j : ℝ) * e j| < 1 / 2) :
    mFourier n (fun j : Fin d => ((tau * e j : ℝ) : UnitAddCircle)) ≠ 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  set u : ℝ := tau * ∑ j : Fin d, (n j : ℝ) * e j
  have hsum : (∑ j : Fin d, 2 * ↑Real.pi * Complex.I * ↑(n j) * ↑(tau * e j)) =
      ↑u * (2 * ↑Real.pi * Complex.I) := by
    simp only [u, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_intCast]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  intro heq
  rw [Complex.exp_eq_one_iff] at heq
  obtain ⟨m, hm⟩ := heq
  have hpi : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hu_eq : (u : ℂ) = (m : ℂ) := mul_right_cancel₀ hpi hm
  have hu_real : u = (m : ℝ) := by exact_mod_cast hu_eq
  rw [hu_real] at hpos hlt
  rcases eq_or_ne m 0 with rfl | hm0
  · simp at hpos
  · have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
    linarith

private lemma integral_mFourier_eq_zero {d : ℕ} {n : Fin d → ℤ} (hn : n ≠ 0) :
    (∫ x : UnitAddTorus (Fin d), mFourier n x) = 0 := by
  have hj : ∃ j : Fin d, n j ≠ 0 := by
    by_contra h
    exact hn (funext fun j => Decidable.byContradiction fun hnj => h ⟨j, hnj⟩)
  obtain ⟨j₀, hj₀⟩ := hj
  let a : UnitAddCircle := ↑((1 : ℝ) / 2 / (n j₀ : ℝ))
  let δ : UnitAddTorus (Fin d) := Function.update 0 j₀ a
  have hshift : ∀ x : UnitAddTorus (Fin d), mFourier n (x + δ) = -mFourier n x := by
    intro x
    simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j₀),
        ← Finset.prod_erase_mul _ _ (Finset.mem_univ j₀)]
    have hrest : ∏ i ∈ Finset.univ.erase j₀, fourier (n i) (x i + δ i) =
        ∏ i ∈ Finset.univ.erase j₀, fourier (n i) (x i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      simp [δ, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    have hmain : fourier (n j₀) (x j₀ + δ j₀) = -fourier (n j₀) (x j₀) := by
      simp only [δ, Function.update_self, a]
      exact fourier_add_half_inv_index hj₀ zero_lt_one (x j₀)
    rw [hrest, hmain, mul_neg]
  have hint : (∫ x : UnitAddTorus (Fin d), mFourier n (x + δ)) =
      ∫ x : UnitAddTorus (Fin d), mFourier n x :=
    integral_add_right_eq_self (fun x => mFourier n x) δ
  simp_rw [hshift, integral_neg] at hint
  have h2 : (2 : ℂ) * (∫ x : UnitAddTorus (Fin d), mFourier n x) = 0 := by linear_combination -hint
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

private lemma kronecker_pos {d : ℕ} (e : Fin d → ℝ) (he : LinearIndependent ℚ e)
    (θ : Fin d → UnitAddCircle) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 ≤ t ∧ ∀ j : Fin d, dist ((t * e j : ℝ) : UnitAddCircle) (θ j) < ε := by
  by_contra h_no
  have h_far : ∀ t : ℝ, 0 ≤ t →
      ε ≤ dist (fun j : Fin d => ((t * e j : ℝ) : UnitAddCircle)) θ := by
    intro t ht
    by_contra hlt
    have hlt' := lt_of_not_ge hlt
    rw [dist_pi_lt_iff hε] at hlt'
    exact h_no ⟨t, ht, hlt'⟩
  let f_real : UnitAddTorus (Fin d) → ℝ := fun x => max 0 (ε - dist x θ)
  have hf_cont : Continuous f_real :=
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have hf_int : Integrable f_real volume :=
    hf_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f_real)
  have hf_nonneg : 0 ≤ f_real := fun _ => le_max_left 0 _
  have hf_theta : f_real θ ≠ 0 := by
    simp only [f_real, dist_self, sub_zero, max_eq_right hε.le]; exact ne_of_gt hε
  let I : ℝ := ∫ x : UnitAddTorus (Fin d), f_real x
  have hI : 0 < I :=
    integral_pos_of_integrable_nonneg_nonzero hf_cont hf_int hf_nonneg hf_theta
  let V : ℝ := (volume : Measure (UnitAddTorus (Fin d))).real univ
  have hV_pos : 0 < V := by
    dsimp [V, Measure.real]
    exact ENNReal.toReal_pos
      (IsOpen.measure_ne_zero volume isOpen_univ ⟨0, trivial⟩) (measure_ne_top volume univ)
  let δ : ℝ := I / (3 * V)
  have hδ_pos : 0 < δ := div_pos hI (by positivity)
  let fC : C(UnitAddTorus (Fin d), ℂ) :=
    ⟨fun x => (f_real x : ℂ), Complex.continuous_ofReal.comp hf_cont⟩
  obtain ⟨P, F, c, h0F, hP_norm, hP_eval⟩ := exists_mFourier_approx fC hδ_pos
  let S : Finset (Fin d → ℤ) := F.erase 0
  have hint_P : (∫ x : UnitAddTorus (Fin d), P x) = (V : ℂ) * c 0 := by
    have h_eq_fn : (fun x : UnitAddTorus (Fin d) => P x) =
        fun x => ∑ n ∈ F, c n * mFourier n x := funext hP_eval
    rw [h_eq_fn]
    rw [integral_finsetSum F (fun n _ => ((mFourier n).continuous.const_mul (c n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    rw [← Finset.add_sum_erase F _ h0F]
    have h0 : (∫ x : UnitAddTorus (Fin d), c 0 * mFourier 0 x) = (V : ℂ) * c 0 := by
      have hm0 : (fun x : UnitAddTorus (Fin d) => c 0 * mFourier 0 x) = fun _ => c 0 := by
        ext x; simp [mFourier_zero]
      rw [hm0, integral_const]; simp [V, Complex.real_smul]
    have hS : ∑ n ∈ S, (∫ x : UnitAddTorus (Fin d), c n * mFourier n x) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [integral_const_mul, integral_mFourier_eq_zero (Finset.ne_of_mem_erase hn), mul_zero]
    rw [h0, hS, add_zero]
  have hint_fC : (∫ x : UnitAddTorus (Fin d), fC x) = (I : ℂ) := integral_ofReal
  have hc0_diff : ‖(V : ℂ) * c 0 - (I : ℂ)‖ ≤ V * ‖P - fC‖ := by
    rw [← hint_P, ← hint_fC, ← integral_sub
      (P.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (fC.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    calc ‖∫ x : UnitAddTorus (Fin d), (P x - fC x)‖
        ≤ ∫ x : UnitAddTorus (Fin d), ‖P x - fC x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : UnitAddTorus (Fin d), ‖P - fC‖ := by
          refine integral_mono
            (((P - fC).continuous.norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            (integrable_const _) (fun x => ContinuousMap.norm_coe_le_norm (P - fC) x)
      _ = V * ‖P - fC‖ := by rw [integral_const, smul_eq_mul]
  have hc0_gt : 2 * δ < ‖c 0‖ := by
    have hI_norm : ‖(I : ℂ)‖ = I := Complex.norm_of_nonneg hI.le
    have hVc_norm : ‖(V : ℂ) * c 0‖ = V * ‖c 0‖ := by
      rw [norm_mul, Complex.norm_of_nonneg hV_pos.le]
    have htri : ‖(I : ℂ)‖ - ‖(V : ℂ) * c 0‖ ≤ ‖(V : ℂ) * c 0 - (I : ℂ)‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le (I : ℂ) ((V : ℂ) * c 0)
    have hVP : V * ‖P - fC‖ < I / 3 := by
      have := mul_lt_mul_of_pos_left hP_norm hV_pos
      have hVδ : V * δ = I / 3 := by dsimp [δ]; field_simp [ne_of_gt hV_pos]
      linarith
    have hVc_gt : 2 * I / 3 < V * ‖c 0‖ := by linarith
    have h2δ : 2 * δ = (2 * I / 3) / V := by dsimp [δ]; ring
    rw [h2δ, div_lt_iff₀ hV_pos]; linarith
  let ω : (Fin d → ℤ) → ℝ := fun n => ∑ j : Fin d, (n j : ℝ) * e j
  have hω_pos : ∀ n ∈ S, 0 < |ω n| := by
    intro n hn
    have hn_ne : n ≠ 0 := Finset.ne_of_mem_erase hn
    rw [abs_pos]; intro h0
    have hlin : ∑ j : Fin d, (n j : ℚ) • e j = 0 := by simpa [ω, Rat.smul_def] using h0
    have hall := Fintype.linearIndependent_iff.mp he (fun j => (n j : ℚ)) hlin
    apply hn_ne; ext j; exact_mod_cast hall j
  let Mω : ℝ := (∑ n ∈ S, |ω n|) + 1
  have hMω_pos : 0 < Mω :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => abs_nonneg _) zero_lt_one
  let tau : ℝ := 1 / (2 * Mω)
  have htau_pos : 0 < tau := by positivity
  let γ₁ : UnitAddTorus (Fin d) := fun j => ((tau * e j : ℝ) : UnitAddCircle)
  let z : (Fin d → ℤ) → ℂ := fun n => mFourier n γ₁
  have hz_ne : ∀ n ∈ S, z n ≠ 1 := by
    intro n hn
    apply mFourier_ray_ne_one e n tau
    · rw [abs_mul, abs_of_pos htau_pos]; exact mul_pos htau_pos (hω_pos n hn)
    · rw [abs_mul, abs_of_pos htau_pos]
      have hle : |ω n| ≤ ∑ m ∈ S, |ω m| :=
        Finset.single_le_sum (f := fun m : Fin d → ℤ => |ω m|) (fun _ _ => abs_nonneg _) hn
      have hltM : |ω n| < Mω := by dsimp [Mω]; linarith
      dsimp [tau]; rw [one_div_mul_eq_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
  have hz_norm : ∀ n : Fin d → ℤ, ‖z n‖ = 1 := by
    intro n
    simp only [z, mFourier, ContinuousMap.coe_mk, fourier_apply, norm_prod, Circle.norm_coe,
      Finset.prod_const_one]
  let B : ℝ := ∑ n ∈ S, ‖c n‖ * (2 / ‖z n - 1‖)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (B / δ)
  let N : ℕ := N₀ + 1
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hBN : B / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hN_pos]
    have hlt' := (div_lt_iff₀ hδ_pos).mp hN₀
    have hN_ge : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_succ N₀
    nlinarith
  let A : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ m ∈ Finset.range N, P (m • γ₁)
  have hγ_eq : ∀ m : ℕ, (m • γ₁ : UnitAddTorus (Fin d)) =
      fun j => ((((m : ℝ) * tau) * e j : ℝ) : UnitAddCircle) := by
    intro m; ext j
    simp only [Pi.smul_apply, γ₁, mul_assoc, ← QuotientAddGroup.mk_nsmul, nsmul_eq_mul]
  have hA_lt : ‖A‖ < δ := by
    dsimp [A]
    rw [norm_mul, Complex.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
    calc (1 / (N : ℝ)) * ‖∑ m ∈ Finset.range N, P (m • γ₁)‖
        ≤ (1 / (N : ℝ)) * ∑ m ∈ Finset.range N, ‖P (m • γ₁)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (1 / (N : ℝ)) * ∑ _ ∈ Finset.range N, ‖P - fC‖ := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => ?_) (by positivity)
          have hf0 : fC (m • γ₁) = 0 := by
            simp only [fC, ContinuousMap.coe_mk, Complex.ofReal_eq_zero, f_real, max_eq_left_iff,
              sub_nonpos, hγ_eq m]
            exact h_far ((m : ℝ) * tau) (by positivity)
          have hsub : P (m • γ₁) = (P - fC) (m • γ₁) := by simp [hf0]
          rw [hsub]; exact ContinuousMap.norm_coe_le_norm (P - fC) (m • γ₁)
      _ = ‖P - fC‖ := by simp [Finset.sum_const, Finset.card_range, ne_of_gt hN_pos]
      _ < δ := hP_norm
  have hA_decomp : A - c 0 = ((1 / (N : ℝ) : ℝ) : ℂ) *
      ∑ n ∈ S, c n * ∑ m ∈ Finset.range N, (z n) ^ m := by
    dsimp [A]
    have hsum1 : (∑ m ∈ Finset.range N, P (m • γ₁)) =
        (N : ℂ) * c 0 + ∑ n ∈ S, c n * ∑ m ∈ Finset.range N, (z n) ^ m := by
      simp_rw [hP_eval]; rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ h0F]
      congr 1
      · simp [mFourier_zero, Finset.sum_const, Finset.card_range]
      · refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.mul_sum]; congr 1
        exact Finset.sum_congr rfl fun m _ => mFourier_eval_nsmul n m γ₁
    rw [hsum1, mul_add]
    have hN_inv : ((1 / (N : ℝ) : ℝ) : ℂ) * (N : ℂ) = 1 := by
      exact_mod_cast one_div_mul_cancel (ne_of_gt hN_pos)
    linear_combination c 0 * hN_inv
  have hA_tail : ‖A - c 0‖ ≤ B / (N : ℝ) := by
    rw [hA_decomp, norm_mul, Complex.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)),
      one_div_mul_eq_div]
    refine div_le_div_of_nonneg_right ?_ hN_pos.le
    calc ‖∑ n ∈ S, c n * ∑ m ∈ Finset.range N, (z n) ^ m‖
        ≤ ∑ n ∈ S, ‖c n * ∑ m ∈ Finset.range N, (z n) ^ m‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S, ‖c n‖ * (2 / ‖z n - 1‖) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [norm_mul]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [geom_sum_eq (hz_ne n hn), norm_div]
          refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
          calc ‖(z n) ^ N - 1‖ ≤ ‖(z n) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [norm_pow, hz_norm n, one_pow, norm_one]; norm_num
  have hA_ge : ‖c 0‖ - ‖A‖ ≤ ‖A - c 0‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le (c 0) A
  linarith

private lemma exists_rat_li_span : ∀ (m : ℕ) (u : Fin m → ℝ),
    ∃ (d : ℕ) (b : Fin d → ℝ) (q : Fin m → Fin d → ℚ),
      LinearIndependent ℚ b ∧ ∀ i : Fin m, u i = ∑ j : Fin d, (q i j : ℝ) * b j
  | 0, u =>
    ⟨0, Fin.elim0, fun i => Fin.elim0 i, linearIndependent_empty_type, fun i => Fin.elim0 i⟩
  | m + 1, u => by
    obtain ⟨d, b, q, hb_li, hq⟩ := exists_rat_li_span m (Fin.init u)
    by_cases h_mem : ∃ r : Fin d → ℚ, u (Fin.last m) = ∑ j : Fin d, (r j : ℝ) * b j
    · obtain ⟨r, hr⟩ := h_mem
      refine ⟨d, b, Fin.snoc q r, hb_li, fun i => ?_⟩
      refine Fin.lastCases ?_ (fun i₀ => ?_) i
      · simpa [Fin.snoc_last] using hr
      · simpa [Fin.snoc_castSucc, Fin.init] using hq i₀
    · let b' : Fin (d + 1) → ℝ := Fin.snoc b (u (Fin.last m))
      have hb'_li : LinearIndependent ℚ b' := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        rw [Fin.sum_univ_castSucc] at hg
        simp only [b', Fin.snoc_castSucc, Fin.snoc_last] at hg
        have hlast : g (Fin.last d) = 0 := by
          by_contra hne
          apply h_mem
          refine ⟨fun j => -g j.castSucc / g (Fin.last d), ?_⟩
          have hne_r : (g (Fin.last d) : ℝ) ≠ 0 := by exact_mod_cast hne
          have hsum_r : (∑ j : Fin d, (g j.castSucc : ℝ) * b j) +
              (g (Fin.last d) : ℝ) * u (Fin.last m) = 0 := by simpa [Rat.smul_def] using hg
          have hu_eq : u (Fin.last m) = -(∑ j : Fin d, (g j.castSucc : ℝ) * b j) / (g (Fin.last d) : ℝ) := by
            field_simp [hne_r]; linarith
          rw [hu_eq, neg_div, Finset.sum_div]
          simp only [← Finset.sum_neg_distrib, Rat.cast_div, Rat.cast_neg]
          refine Finset.sum_congr rfl fun j _ => by ring
        have hg_init : ∑ j : Fin d, g j.castSucc • b j = 0 := by
          rw [hlast, zero_smul, add_zero] at hg; exact hg
        have hinit := Fintype.linearIndependent_iff.mp hb_li (fun j => g j.castSucc) hg_init
        intro j; refine Fin.lastCases hlast hinit j
      let q' : Fin (m + 1) → Fin (d + 1) → ℚ :=
        Fin.snoc (fun i₀ => Fin.snoc (q i₀) 0) (Fin.snoc (fun _ => 0) 1)
      refine ⟨d + 1, b', q', hb'_li, fun i => ?_⟩
      refine Fin.lastCases ?_ (fun i₀ => ?_) i
      · rw [Fin.sum_univ_castSucc]; simp [q', b', Fin.snoc_last, Fin.snoc_castSucc]
      · rw [Fin.sum_univ_castSucc]; simpa [q', b', Fin.snoc_last, Fin.snoc_castSucc, Fin.init] using hq i₀

private lemma exists_int_coords_over_rat_li {k : ℕ} (v : Fin k → ℝ) :
    ∃ (d : ℕ) (e : Fin d → ℝ) (c : Fin k → Fin d → ℤ),
      LinearIndependent ℚ e ∧ ∀ i : Fin k, v i = ∑ j : Fin d, (c i j : ℝ) * e j := by
  obtain ⟨d, b, q, hb_li, hq⟩ := exists_rat_li_span k v
  let D : ℕ := ∏ i : Fin k, ∏ j : Fin d, (q i j).den
  have hD_pos : 0 < D := Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (q i j).pos
  have hD_ne_q : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hD_pos)
  have hD_ne_r : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hD_pos)
  let e : Fin d → ℝ := fun j => b j / (D : ℝ)
  have he_li : LinearIndependent ℚ e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∑ j : Fin d, (g j / (D : ℚ)) • b j = 0 := by
      rw [← hg]; refine Finset.sum_congr rfl fun j _ => ?_
      simp only [e, Rat.smul_def, Rat.cast_div, Rat.cast_natCast]; ring
    have hall := Fintype.linearIndependent_iff.mp hb_li (fun j => g j / (D : ℚ)) hg'
    intro j; exact (div_eq_zero_iff.mp (hall j)).resolve_right hD_ne_q
  let q_div : Fin k → Fin d → ℕ := fun i j => D / (q i j).den
  let c : Fin k → Fin d → ℤ := fun i j => (q i j).num * (q_div i j : ℤ)
  have hc_eq : ∀ (i : Fin k) (j : Fin d), (c i j : ℚ) = (D : ℚ) * q i j := by
    intro i j
    have hdvd1 : (q i j).den ∣ ∏ j' : Fin d, (q i j').den :=
      Finset.dvd_prod_of_mem (fun j' : Fin d => (q i j').den) (Finset.mem_univ j)
    have hdvd2 : (∏ j' : Fin d, (q i j').den) ∣ D :=
      Finset.dvd_prod_of_mem (fun i' : Fin k => ∏ j' : Fin d, (q i' j').den) (Finset.mem_univ i)
    have hdvd : (q i j).den ∣ D := dvd_trans hdvd1 hdvd2
    have hmul : (q_div i j : ℚ) * ((q i j).den : ℚ) = (D : ℚ) := by
      dsimp [q_div]; exact_mod_cast Nat.div_mul_cancel hdvd
    have hden_ne : ((q i j).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (q i j).pos)
    apply mul_right_cancel₀ hden_ne
    have hnum : q i j * ((q i j).den : ℚ) = ((q i j).num : ℚ) := Rat.mul_den_eq_num (q i j)
    calc (c i j : ℚ) * ((q i j).den : ℚ)
        = ((q i j).num : ℚ) * ((q_div i j : ℚ) * ((q i j).den : ℚ)) := by
          dsimp only [c]; rw [Int.cast_mul, Int.cast_natCast, mul_assoc]
      _ = ((q i j).num : ℚ) * (D : ℚ) := by rw [hmul]
      _ = (D : ℚ) * (q i j * ((q i j).den : ℚ)) := by rw [hnum, mul_comm]
      _ = ((D : ℚ) * q i j) * ((q i j).den : ℚ) := by ring
  refine ⟨d, e, c, he_li, fun i => ?_⟩
  rw [hq i]; refine Finset.sum_congr rfl fun j _ => ?_
  have hcj_r : (c i j : ℝ) = (D : ℝ) * (q i j : ℝ) := by exact_mod_cast hc_eq i j
  rw [hcj_r]; dsimp [e]; field_simp [hD_ne_r]

private lemma dist_zsmul_unitAddCircle_le (n : ℤ) (x y : UnitAddCircle) :
    dist (n • x) (n • y) ≤ |(n : ℝ)| * dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← zsmul_sub]
  have hnat : ∀ (m : ℕ) (z : UnitAddCircle), ‖m • z‖ ≤ (m : ℝ) * ‖z‖ := fun _ _ => norm_nsmul_le
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    simpa [abs_of_nonneg hm0] using hnat m (x - y)
  · have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [neg_zsmul, norm_neg, Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg hm0]
    exact hnat m (x - y)

private lemma dist_sum_zsmul_le {d : ℕ} (c : Fin d → ℤ) (x y : Fin d → UnitAddCircle) :
    dist (∑ j : Fin d, c j • x j) (∑ j : Fin d, c j • y j) ≤
      ∑ j : Fin d, |(c j : ℝ)| * dist (x j) (y j) := by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc ‖∑ j : Fin d, (c j • x j - c j • y j)‖
      ≤ ∑ j : Fin d, ‖c j • x j - c j • y j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin d, |(c j : ℝ)| * dist (x j) (y j) :=
        Finset.sum_le_sum fun j _ => dist_eq_norm (c j • x j) (c j • y j) ▸
          dist_zsmul_unitAddCircle_le (c j) (x j) (y j)

private lemma mk_sum_int_mul {d : ℕ} (c : Fin d → ℤ) (x : Fin d → ℝ) :
    ((∑ j : Fin d, (c j : ℝ) * x j : ℝ) : UnitAddCircle) =
      ∑ j : Fin d, c j • ((x j : ℝ) : UnitAddCircle) := by
  rw [QuotientAddGroup.mk_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← QuotientAddGroup.mk_zsmul, zsmul_eq_mul]

private lemma clear_pos_rat_denoms {m : ℕ} (r : Fin m → ℚ) (hr_pos : ∀ i : Fin m, 0 < r i) :
    ∃ (M : ℕ) (a : Fin m → ℕ), 0 < M ∧ (∀ i : Fin m, 0 < a i) ∧
      ∀ i : Fin m, (a i : ℚ) = (M : ℚ) * r i := by
  let M : ℕ := ∏ i : Fin m, (r i).den
  have hM_pos : 0 < M := Finset.prod_pos fun i _ => (r i).pos
  let m_div : Fin m → ℕ := fun i => M / (r i).den
  let z : Fin m → ℤ := fun i => (r i).num * (m_div i : ℤ)
  have hz_eq : ∀ i : Fin m, (z i : ℚ) = (M : ℚ) * r i := by
    intro i
    have hdvd : (r i).den ∣ M :=
      Finset.dvd_prod_of_mem (fun i' : Fin m => (r i').den) (Finset.mem_univ i)
    have hmul : (m_div i : ℚ) * ((r i).den : ℚ) = (M : ℚ) := by
      dsimp [m_div]; exact_mod_cast Nat.div_mul_cancel hdvd
    have hden_ne : ((r i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (r i).pos)
    apply mul_right_cancel₀ hden_ne
    have hnum : r i * ((r i).den : ℚ) = ((r i).num : ℚ) := Rat.mul_den_eq_num (r i)
    calc (z i : ℚ) * ((r i).den : ℚ)
        = ((r i).num : ℚ) * ((m_div i : ℚ) * ((r i).den : ℚ)) := by
          dsimp only [z]; rw [Int.cast_mul, Int.cast_natCast, mul_assoc]
      _ = ((r i).num : ℚ) * (M : ℚ) := by rw [hmul]
      _ = (M : ℚ) * (r i * ((r i).den : ℚ)) := by rw [hnum, mul_comm]
      _ = ((M : ℚ) * r i) * ((r i).den : ℚ) := by ring
  have hz_pos : ∀ i : Fin m, 0 < z i := by
    intro i
    exact Int.cast_pos.mp (hz_eq i ▸ mul_pos (Nat.cast_pos.mpr hM_pos) (hr_pos i))
  refine ⟨M, fun i => (z i).toNat, hM_pos, fun i => Int.pos_iff_toNat_pos.mp (hz_pos i), fun i => ?_⟩
  have htonat : ((z i).toNat : ℤ) = z i := Int.toNat_of_nonneg (hz_pos i).le
  calc (((z i).toNat : ℕ) : ℚ) = ((z i : ℤ) : ℚ) := by exact_mod_cast htonat
    _ = (M : ℚ) * r i := hz_eq i

private theorem real_to_nat_lrc (k : ℕ) (hk : 2 ≤ k) (v : Fin k → ℝ)
    (hv_pos : ∀ i : Fin k, 0 < v i) (hv_mono : StrictMono v)
    (h_int : ∀ (m : ℕ), 1 ≤ m → m ≤ k → ∀ (w : Fin m → ℕ),
      (∀ i : Fin m, 0 < w i) → StrictMono w →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  let i₀ : Fin k := ⟨0, by omega⟩
  have hv0 : 0 < v i₀ := hv_pos i₀
  by_cases h_prop : ∀ i : Fin k, ∃ r : ℚ, v i = (r : ℝ) * v i₀
  · choose r hr using h_prop
    have hr_pos : ∀ i : Fin k, 0 < r i := fun i =>
      Rat.cast_pos.mp (pos_of_mul_pos_left (hr i ▸ hv_pos i) hv0.le)
    obtain ⟨M, w, hM_pos, hw_pos, hw_eq⟩ := clear_pos_rat_denoms r hr_pos
    have hw_real : ∀ i : Fin k, (w i : ℝ) * v i₀ = (M : ℝ) * v i := by
      intro i
      have hw_r : (w i : ℝ) = (M : ℝ) * (r i : ℝ) := by exact_mod_cast hw_eq i
      rw [hw_r, hr i, mul_assoc]
    have hw_mono : StrictMono w := by
      intro i j hij
      have hlt_v : (M : ℝ) * v i < (M : ℝ) * v j :=
        mul_lt_mul_of_pos_left (hv_mono hij) (Nat.cast_pos.mpr hM_pos)
      rw [← hw_real i, ← hw_real j] at hlt_v
      exact Nat.cast_lt.mp (lt_of_mul_lt_mul_right hlt_v hv0.le)
    obtain ⟨t', ht'0, ht'⟩ := h_int k (by omega) le_rfl w hw_pos hw_mono
    refine ⟨t' * (M : ℝ) / v i₀, by positivity, fun i => ?_⟩
    have hmul : t' * (M : ℝ) / v i₀ * v i = t' * (w i : ℝ) := by
      have h1 : (M : ℝ) * v i = (w i : ℝ) * v i₀ := (hw_real i).symm
      calc t' * (M : ℝ) / v i₀ * v i = t' * ((M : ℝ) * v i) / v i₀ := by ring
        _ = t' * ((w i : ℝ) * v i₀) / v i₀ := by rw [h1]
        _ = t' * (w i : ℝ) := by field_simp [ne_of_gt hv0]
    rw [hmul]; exact ht' i
  · obtain ⟨d, e, c, he_li, hve⟩ := exists_int_coords_over_rat_li v
    let Csum : ℝ := (∑ i : Fin k, ∑ j : Fin d, |(c i j : ℝ)|) + 1
    have hCsum_pos : 0 < Csum := add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) zero_lt_one
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * Csum / v i₀)
    let N : ℕ := N₀ + 1
    have hN_pos_r : (0 : ℝ) < (N : ℝ) := by positivity
    let r : Fin d → ℚ := fun j => (⌊(N : ℝ) * e j⌋ : ℚ) / (N : ℚ)
    have hr_approx : ∀ j : Fin d, |(r j : ℝ) - e j| ≤ 1 / (N : ℝ) := by
      intro j
      have hfl1 : (⌊(N : ℝ) * e j⌋ : ℝ) ≤ (N : ℝ) * e j := Int.floor_le _
      have hfl2 : (N : ℝ) * e j < (⌊(N : ℝ) * e j⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have hr_cast : (r j : ℝ) = (⌊(N : ℝ) * e j⌋ : ℝ) / (N : ℝ) := by dsimp [r]; push_cast; rfl
      have heq : (r j : ℝ) - e j = ((⌊(N : ℝ) * e j⌋ : ℝ) - (N : ℝ) * e j) / (N : ℝ) := by
        rw [hr_cast]; field_simp [ne_of_gt hN_pos_r]
      rw [heq, abs_div, abs_of_pos hN_pos_r]
      exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) hN_pos_r.le
    let rStar : Fin k → ℚ := fun i => ∑ j : Fin d, (c i j : ℚ) * r j
    have hrStar_pos : ∀ i : Fin k, 0 < rStar i := by
      intro i
      have hvi_ge : v i₀ ≤ v i := by
        rcases eq_or_lt_of_le (Nat.zero_le i.val) with h0 | hpos
        · exact (Fin.ext h0.symm : i = i₀) ▸ le_rfl
        · exact (hv_mono (by rw [Fin.lt_def]; exact hpos)).le
      have hdiff : |(rStar i : ℝ) - v i| ≤ Csum / (N : ℝ) := by
        have hcast : (rStar i : ℝ) - v i = ∑ j : Fin d, (c i j : ℝ) * ((r j : ℝ) - e j) := by
          rw [hve i]; dsimp [rStar]; push_cast; rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hcast]
        calc |∑ j : Fin d, (c i j : ℝ) * ((r j : ℝ) - e j)|
            ≤ ∑ j : Fin d, |(c i j : ℝ) * ((r j : ℝ) - e j)| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j : Fin d, |(c i j : ℝ)| * |(r j : ℝ) - e j| :=
              Finset.sum_congr rfl fun j _ => abs_mul _ _
          _ ≤ ∑ j : Fin d, |(c i j : ℝ)| * (1 / (N : ℝ)) :=
              Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hr_approx j) (abs_nonneg _)
          _ = (∑ j : Fin d, |(c i j : ℝ)|) / (N : ℝ) := by rw [← Finset.sum_mul, mul_one_div]
          _ ≤ Csum / (N : ℝ) := by
              refine div_le_div_of_nonneg_right ?_ hN_pos_r.le
              have hle_i := Finset.single_le_sum (f := fun i' : Fin k => ∑ j : Fin d, |(c i' j : ℝ)|)
                (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
              dsimp [Csum]; linarith
      have hCN : Csum / (N : ℝ) < v i₀ / 2 := by
        rw [div_lt_div_iff₀ hN_pos_r zero_lt_two]
        have h1 := (div_lt_iff₀ hv0).mp hN₀
        have h2 : (N₀ : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_succ_self N₀
        nlinarith
      have hpos_r : (0 : ℝ) < (rStar i : ℝ) := by
        have := (abs_le.mp hdiff).1
        linarith
      exact Rat.cast_pos.mp hpos_r
    have hex_col : ∃ (j₀ : Fin d) (i : Fin k),
        (c i j₀ : ℚ) / rStar i ≠ (c i₀ j₀ : ℚ) / rStar i₀ := by
      by_contra h_all; apply h_prop; intro i
      refine ⟨rStar i / rStar i₀, ?_⟩
      have hr0_ne : (rStar i₀ : ℝ) ≠ 0 := ne_of_gt (Rat.cast_pos.mpr (hrStar_pos i₀))
      have h_col_eq : ∀ j : Fin d, (c i j : ℝ) * (rStar i₀ : ℝ) = (c i₀ j : ℝ) * (rStar i : ℝ) := by
        intro j
        have h_eq_q : (c i j : ℚ) / rStar i = (c i₀ j : ℚ) / rStar i₀ :=
          Decidable.byContradiction fun hne => h_all ⟨j, i, hne⟩
        have h_mul_q := (div_eq_div_iff (ne_of_gt (hrStar_pos i)) (ne_of_gt (hrStar_pos i₀))).mp h_eq_q
        exact_mod_cast h_mul_q
      have hsum_eq : v i * (rStar i₀ : ℝ) = (rStar i : ℝ) * v i₀ := by
        rw [hve i, hve i₀, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        calc ((c i j : ℝ) * e j) * (rStar i₀ : ℝ)
            = ((c i j : ℝ) * (rStar i₀ : ℝ)) * e j := by ring
          _ = ((c i₀ j : ℝ) * (rStar i : ℝ)) * e j := by rw [h_col_eq j]
          _ = (rStar i : ℝ) * ((c i₀ j : ℝ) * e j) := by ring
      push_cast; field_simp [hr0_ne]; linarith
    obtain ⟨j₀, i_neq, hi_neq⟩ := hex_col
    let f : Fin k → ℚ := fun i => (c i j₀ : ℚ) / rStar i
    let Sf : Finset ℚ := Finset.univ.image f
    have hSf_ne : Sf.Nonempty := ⟨f i₀, Finset.mem_image_of_mem f (Finset.mem_univ i₀)⟩
    let q1 : ℚ := Sf.min' hSf_ne
    obtain ⟨i₁, _, hi₁_eq⟩ := Finset.mem_image.mp (Finset.min'_mem Sf hSf_ne)
    have hex_gt : ∃ x ∈ Sf, q1 < x := by
      have hf0_mem : f i₀ ∈ Sf := Finset.mem_image_of_mem f (Finset.mem_univ i₀)
      have hfi_mem : f i_neq ∈ Sf := Finset.mem_image_of_mem f (Finset.mem_univ i_neq)
      rcases lt_or_eq_of_le (Finset.min'_le Sf (f i₀) hf0_mem) with hlt0 | heq0
      · exact ⟨f i₀, hf0_mem, hlt0⟩
      · refine ⟨f i_neq, hfi_mem, lt_of_le_of_ne (Finset.min'_le Sf (f i_neq) hfi_mem) ?_⟩
        exact fun heqi => hi_neq (heqi.symm.trans heq0)
    let Sf_gt : Finset ℚ := Sf.filter (fun x => q1 < x)
    have hSf_gt_ne : Sf_gt.Nonempty := by
      obtain ⟨x, hx, hlt⟩ := hex_gt; exact ⟨x, Finset.mem_filter.mpr ⟨hx, hlt⟩⟩
    let q2 : ℚ := Sf_gt.min' hSf_gt_ne
    obtain ⟨hq2_Sf, hq1_lt_q2⟩ := Finset.mem_filter.mp (Finset.min'_mem Sf_gt hSf_gt_ne)
    obtain ⟨i₂, _, hi₂_eq⟩ := Finset.mem_image.mp hq2_Sf
    have hi₁_ne_i₂ : i₁ ≠ i₂ := fun heq => by
      rw [heq, hi₂_eq] at hi₁_eq
      linarith [hq1_lt_q2, hi₁_eq]
    have hf_gap : ∀ i : Fin k, f i ≤ f i₁ ∨ f i₂ ≤ f i := by
      intro i; rw [hi₁_eq, hi₂_eq]
      rcases le_or_gt (f i) q1 with hle | hgt
      · exact Or.inl hle
      · exact Or.inr (Finset.min'_le Sf_gt (f i)
          (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem f (Finset.mem_univ i), hgt⟩))
    let η : Fin d → ℚ := fun j =>
      (if j = j₀ then rStar i₁ + rStar i₂ else 0) - ((c i₁ j₀ : ℚ) + (c i₂ j₀ : ℚ)) * r j
    let wStar : Fin k → ℚ := fun i => ∑ j : Fin d, (c i j : ℚ) * η j
    have hwStar_formula : ∀ i : Fin k,
        wStar i = (rStar i₁ + rStar i₂) * (c i j₀ : ℚ) -
          ((c i₁ j₀ : ℚ) + (c i₂ j₀ : ℚ)) * rStar i := by
      intro i; dsimp [wStar, η, rStar]; simp_rw [mul_sub, Finset.sum_sub_distrib]
      congr 1
      · simp [mul_comm]
      · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have hwStar_collide : |wStar i₁| = |wStar i₂| := by
      have hsum0 : wStar i₁ + wStar i₂ = 0 := by rw [hwStar_formula i₁, hwStar_formula i₂]; ring
      rw [eq_neg_of_add_eq_zero_left hsum0, abs_neg]
    have hwStar_abs_pos : ∀ i : Fin k, 0 < |wStar i| := by
      intro i; rw [abs_pos]; intro hw0; rw [hwStar_formula i] at hw0
      have hr1 := hrStar_pos i₁; have hr2 := hrStar_pos i₂; have hri := hrStar_pos i
      have hf12 : f i₁ < f i₂ := by rwa [hi₁_eq, hi₂_eq]
      have hlt12 : (c i₁ j₀ : ℚ) * rStar i₂ < (c i₂ j₀ : ℚ) * rStar i₁ := by
        dsimp [f] at hf12; rwa [div_lt_div_iff₀ hr1 hr2] at hf12
      rcases hf_gap i with hle1 | hge2
      · dsimp [f] at hle1; have := (div_le_div_iff₀ hri hr1).mp hle1; nlinarith
      · dsimp [f] at hge2; have := (div_le_div_iff₀ hr2 hri).mp hge2; nlinarith
    obtain ⟨Mw, a, _, ha_pos, ha_eq⟩ := clear_pos_rat_denoms (fun i => |wStar i|) hwStar_abs_pos
    have ha_collide : a i₁ = a i₂ :=
      Nat.cast_injective (by rw [ha_eq i₁, ha_eq i₂, hwStar_collide] : (a i₁ : ℚ) = (a i₂ : ℚ))
    let Aset : Finset ℕ := Finset.univ.image a
    have hA_sub : Aset ⊆ (Finset.univ.erase i₂).image a := by
      intro x hx; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rcases eq_or_ne i i₂ with rfl | hne
      · rw [← ha_collide]
        exact Finset.mem_image.mpr ⟨i₁, Finset.mem_erase.mpr ⟨hi₁_ne_i₂, Finset.mem_univ i₁⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i⟩, rfl⟩
    let m : ℕ := Aset.card
    have hm_pos : 1 ≤ m :=
      Finset.card_pos.mpr ⟨a i₀, Finset.mem_image_of_mem a (Finset.mem_univ i₀)⟩
    have hm_lt : m < k := by
      have h1 := Finset.card_le_card hA_sub
      have h2 := Finset.card_image_le (s := Finset.univ.erase i₂) (f := a)
      have h3 : (Finset.univ.erase i₂).card = k - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i₂), Finset.card_fin]
      omega
    let emb := Aset.orderEmbOfFin rfl
    let w_int : Fin m → ℕ := fun l => emb l
    have hw_int_pos : ∀ l : Fin m, 0 < w_int l := by
      intro l
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.orderEmbOfFin_mem Aset rfl l)
      dsimp [w_int, emb]
      rw [← hi]
      exact ha_pos i
    obtain ⟨t₀, ht₀_nonneg, ht₀_lonely⟩ := h_int m hm_pos hm_lt.le w_int hw_int_pos emb.strictMono
    have ha_lonely : ∀ i : Fin k,
        dist ((t₀ * (Mw : ℝ) * (wStar i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / (k : ℝ) := by
      intro i
      have hmem : a i ∈ (Aset : Set ℕ) :=
        Finset.mem_coe.mpr (Finset.mem_image_of_mem a (Finset.mem_univ i))
      have hrange : Set.range w_int = (Aset : Set ℕ) := Finset.range_orderEmbOfFin Aset rfl
      obtain ⟨l, hl⟩ : ∃ l : Fin m, w_int l = a i := by rwa [← hrange] at hmem
      have hstep := ht₀_lonely l; rw [hl] at hstep
      have ha_r : (a i : ℝ) = (Mw : ℝ) * |(wStar i : ℝ)| := by exact_mod_cast ha_eq i
      have hdist_eq : dist ((t₀ * (Mw : ℝ) * (wStar i : ℝ) : ℝ) : UnitAddCircle) 0 =
          dist ((t₀ * (a i : ℝ) : ℝ) : UnitAddCircle) 0 := by
        rw [ha_r, ← mul_assoc, unitAddCircle_dist_abs]
      rw [hdist_eq]
      have hmk_le : m + 1 ≤ k := by omega
      exact le_trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hmk_le)) hstep
    let θ : Fin d → UnitAddCircle := fun j => ((t₀ * (Mw : ℝ) * (η j : ℝ) : ℝ) : UnitAddCircle)
    have hθ_sum : ∀ i : Fin k,
        ∑ j : Fin d, c i j • θ j = ((t₀ * (Mw : ℝ) * (wStar i : ℝ) : ℝ) : UnitAddCircle) := by
      intro i; dsimp [θ]; rw [← mk_sum_int_mul]; congr 1
      dsimp [wStar]; push_cast; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    let gap : ℝ := 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)
    have hgap_pos : 0 < gap := sub_pos.mpr
      (one_div_lt_one_div_of_lt (by positivity) (by exact_mod_cast Nat.lt_succ_self k))
    let ε : ℝ := gap / (2 * Csum)
    have hε_pos : 0 < ε := div_pos hgap_pos (by positivity)
    obtain ⟨t, ht_nonneg, ht_approx⟩ := kronecker_pos e he_li θ hε_pos
    refine ⟨t, ht_nonneg, fun i => ?_⟩
    have htv_sum : ((t * v i : ℝ) : UnitAddCircle) =
        ∑ j : Fin d, c i j • ((t * e j : ℝ) : UnitAddCircle) := by
      rw [← mk_sum_int_mul, hve i, Finset.mul_sum]; congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    have hclose : dist ((t * v i : ℝ) : UnitAddCircle)
        ((t₀ * (Mw : ℝ) * (wStar i : ℝ) : ℝ) : UnitAddCircle) ≤ gap / 2 := by
      rw [htv_sum, ← hθ_sum i]
      calc dist (∑ j : Fin d, c i j • ((t * e j : ℝ) : UnitAddCircle)) (∑ j : Fin d, c i j • θ j)
          ≤ ∑ j : Fin d, |(c i j : ℝ)| * dist ((t * e j : ℝ) : UnitAddCircle) (θ j) :=
            dist_sum_zsmul_le (c i) _ θ
        _ ≤ ∑ j : Fin d, |(c i j : ℝ)| * ε :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ht_approx j).le (abs_nonneg _)
        _ = (∑ j : Fin d, |(c i j : ℝ)|) * ε := (Finset.sum_mul _ _ _).symm
        _ ≤ Csum * ε := by
            refine mul_le_mul_of_nonneg_right ?_ hε_pos.le
            have hle_i := Finset.single_le_sum (f := fun i' : Fin k => ∑ j : Fin d, |(c i' j : ℝ)|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
            dsimp [Csum]; linarith
        _ = gap / 2 := by dsimp [ε]; field_simp [ne_of_gt hCsum_pos]
    have hbase := ha_lonely i
    have htri : dist ((t₀ * (Mw : ℝ) * (wStar i : ℝ) : ℝ) : UnitAddCircle) 0 ≤
        dist ((t * v i : ℝ) : UnitAddCircle)
          ((t₀ * (Mw : ℝ) * (wStar i : ℝ) : ℝ) : UnitAddCircle) +
        dist ((t * v i : ℝ) : UnitAddCircle) 0 := by
      rw [dist_comm ((t * v i : ℝ) : UnitAddCircle)]; exact dist_triangle _ _ _
    dsimp [gap] at hclose hgap_pos
    linarith

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

private lemma lrc_nat_not_dvd (m : ℕ) (w : Fin m → ℕ)
    (h_ndvd : ∀ i : Fin m, ¬ (m + 1) ∣ w i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  refine ⟨1 / ((m + 1 : ℕ) : ℝ), by positivity, fun i => ?_⟩
  let q : ℕ := w i / (m + 1)
  let r : ℕ := w i % (m + 1)
  have hdiv : (m + 1) * q + r = w i := Nat.div_add_mod (w i) (m + 1)
  have hr_ge : 1 ≤ r :=
    Nat.one_le_iff_ne_zero.mpr (fun hr0 => h_ndvd i (Nat.dvd_of_mod_eq_zero hr0))
  have hr_le : r ≤ m := Nat.le_of_lt_succ (Nat.mod_lt (w i) (Nat.succ_pos m))
  have h_eq : 1 / ((m + 1 : ℕ) : ℝ) * (w i : ℝ) =
      ((q : ℤ) : ℝ) + (r : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    have hwi_cast : (w i : ℝ) = ((m + 1 : ℕ) : ℝ) * (q : ℝ) + (r : ℝ) := by exact_mod_cast hdiv.symm
    rw [hwi_cast, Int.cast_natCast]; field_simp [ne_of_gt hm_pos]
  rw [h_eq]
  have hlo : ((q : ℤ) : ℝ) + 1 / ((m + 1 : ℕ) : ℝ) ≤
      ((q : ℤ) : ℝ) + (r : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge
    linarith [div_le_div_of_nonneg_right hr1 hm_pos.le]
  have hhi : ((q : ℤ) : ℝ) + (r : ℝ) / ((m + 1 : ℕ) : ℝ) ≤
      ((q : ℤ) : ℝ) + 1 - 1 / ((m + 1 : ℕ) : ℝ) := by
    have hrm : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast hr_le
    have hdiv_le : (r : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 - 1 / ((m + 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ hm_pos]
      have hm1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      have h_rhs : (1 - 1 / ((m + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) = (m : ℝ) := by
        field_simp [ne_of_gt hm_pos]; linarith
      linarith
    linarith
  exact unitAddCircle_dist_ge_of_Icc _ (1 / ((m + 1 : ℕ) : ℝ)) (q : ℤ) hlo hhi

-- Rosenfeld's (k - 1)-subset coprimality sieve: if any (m - 1) speeds share a factor > 1,
-- loneliness reduces unconditionally to m - 1 runners via prime-coset shifting.
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
  -- Choose target residue r < p placing fract(t' * w i₀ / p) + r / p at distance ≥ 1/4 from ℤ.
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
  -- Multiplication by w i₀ mod p is injective, hence surjective on Fin p.
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
        t' * (u l : ℝ) + ((s.val * u l : ℕ) : ℝ) := by
      rw [hw_eq]; push_cast; field_simp [ne_of_gt hp_pos_r]
    have h_coe : (((t' + (s.val : ℝ)) / (p : ℝ) * (w i : ℝ) : ℝ) : UnitAddCircle) =
        ((t' * (u l : ℝ) : ℝ) : UnitAddCircle) := by
      rw [h_mul, QuotientAddGroup.mk_add]
      have h1_zero : ((1 : ℝ) : UnitAddCircle) = 0 :=
        (QuotientAddGroup.eq_zero_iff (1 : ℝ)).mpr (AddSubgroup.mem_zmultiples (1 : ℝ))
      have h_int_zero : ((((s.val * u l : ℕ) : ℝ)) : UnitAddCircle) = 0 := by
        rw [← nsmul_one (s.val * u l), QuotientAddGroup.mk_nsmul, h1_zero, smul_zero]
      rw [h_int_zero, add_zero]
    rw [h_coe]
    have hstep := ht'_lonely l
    have hm_sub : m - 1 + 1 = m := by omega
    rw [hm_sub] at hstep
    have hfrac : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 / (m : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (Nat.le_succ m))
    exact le_trans hfrac hstep

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

private lemma lrc_nat_prim_core (h1 : H1) (h3 : H3) (m : ℕ) (hm4 : 4 ≤ m)
    (u : Fin m → ℕ) (hu_pos : ∀ i : Fin m, 0 < u i) (hu_mono : StrictMono u)
    (hu_gcd : Finset.univ.gcd u = 1)
    (h_prev : ∀ (w' : Fin (m - 1) → ℕ), (∀ l : Fin (m - 1), 0 < w' l) → StrictMono w' →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ l : Fin (m - 1), dist ((t * (w' l : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m - 1 + 1 : ℕ) : ℝ))
    (h_small_or_zono : m ≤ 9 ∨
      (10 ≤ m ∧ (∑ S ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅, S.gcd u) ≤
        (Nat.choose (m + 1) 2) ^ (m - 1))) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  by_cases h_sub : ∀ i₀ : Fin m, (Finset.univ.erase i₀).gcd u = 1
  · by_cases hdvd : ∃ i : Fin m, (m + 1) ∣ u i
    · by_cases hlac : ∃ i j : Fin m, i.val + 1 = j.val ∧ j.val + 1 < m ∧
          (m - 1) * u j < 2 * m * u i
      · rcases h_small_or_zono with hm9 | ⟨hm10, hzono⟩
        · exact h1 m hm4 hm9 u hu_pos hu_mono hu_gcd h_sub hdvd hlac
        · exact h3 m hm10 u hu_pos hu_mono hu_gcd h_sub hdvd hlac hzono
      · exact lrc_lacunary_nat m (by omega) u hu_pos hu_mono hlac
    · exact lrc_nat_not_dvd m u (fun i hi => hdvd ⟨i, hi⟩)
  · have hex_bad : ∃ i₀ : Fin m, (Finset.univ.erase i₀).gcd u ≠ 1 := by
      by_contra hno
      exact h_sub (fun i₀ => Decidable.byContradiction fun hne => hno ⟨i₀, hne⟩)
    obtain ⟨i₀, hi₀⟩ := hex_bad
    exact lrc_nat_one_exception_sieve m (by omega) u hu_pos hu_mono hu_gcd i₀ hi₀ h_prev

private lemma lrc_all_nat (h1 : H1) (h2 : H2) (h3 : H3) :
    ∀ (m : ℕ), 1 ≤ m → ∀ (w : Fin m → ℕ),
      (∀ i : Fin m, 0 < w i) → StrictMono w →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm1 w hw_pos hw_mono
    rcases eq_or_ne m 1 with rfl | hm_ne1
    · exact lrc_pos_one (fun i => (w i : ℝ)) (fun i => Nat.cast_pos.mpr (hw_pos i))
    rcases eq_or_ne m 2 with rfl | hm_ne2
    · exact lrc_pos_two (fun i => (w i : ℝ))
        (fun i => Nat.cast_pos.mpr (hw_pos i)) (fun i j hij => Nat.cast_lt.mpr (hw_mono hij))
    rcases eq_or_ne m 3 with rfl | hm_ne3
    · exact lrc_pos_three (fun i => (w i : ℝ))
        (fun i => Nat.cast_pos.mpr (hw_pos i)) (fun i j hij => Nat.cast_lt.mpr (hw_mono hij))
    have hm4 : 4 ≤ m := by omega
    have h_prev : ∀ (u : Fin (m - 1) → ℕ), (∀ l : Fin (m - 1), 0 < u l) → StrictMono u →
        ∃ t : ℝ, t ≥ 0 ∧
          ∀ l : Fin (m - 1), dist ((t * (u l : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m - 1 + 1 : ℕ) : ℝ) :=
      fun u hu_pos hu_mono => ih (m - 1) (by omega) (by omega) u hu_pos hu_mono
    refine lrc_nat_gcd_reduction m hm1 w hw_pos hw_mono ?_
    intro w' hw'_pos hw'_mono hw'_gcd
    rcases le_or_gt m 9 with hm9 | hm9
    · exact lrc_nat_prim_core h1 h3 m hm4 w' hw'_pos hw'_mono hw'_gcd h_prev (Or.inl hm9)
    · have hm10 : 10 ≤ m := by omega
      have h_zono_bdd : ∀ (u : Fin m → ℕ),
          (∀ i : Fin m, 0 < u i) → StrictMono u → Finset.univ.gcd u = 1 →
          (∑ S ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅, S.gcd u) ≤
            (Nat.choose (m + 1) 2) ^ (m - 1) →
          ∃ t : ℝ, t ≥ 0 ∧
            ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) :=
        fun u hu_pos hu_mono hu_gcd hzono =>
          lrc_nat_prim_core h1 h3 m hm4 u hu_pos hu_mono hu_gcd h_prev (Or.inr ⟨hm10, hzono⟩)
      rcases le_or_gt
          (∑ S ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅, S.gcd w')
          ((Nat.choose (m + 1) 2) ^ (m - 1)) with hzono_le | hzono_gt
      · exact h_zono_bdd w' hw'_pos hw'_mono hw'_gcd hzono_le
      · by_cases h_sub : ∀ i₀ : Fin m, (Finset.univ.erase i₀).gcd w' = 1
        · by_cases hdvd : ∃ i : Fin m, (m + 1) ∣ w' i
          · by_cases hlac : ∃ i j : Fin m, i.val + 1 = j.val ∧ j.val + 1 < m ∧
                (m - 1) * w' j < 2 * m * w' i
            · exact h2 m hm10 w' hw'_pos hw'_mono hw'_gcd h_sub hdvd hlac hzono_gt
                (fun m' hm'1 hm'lt u hu_pos hu_mono => ih m' hm'lt hm'1 u hu_pos hu_mono)
                h_zono_bdd
            · exact lrc_lacunary_nat m (by omega) w' hw'_pos hw'_mono hlac
          · exact lrc_nat_not_dvd m w' (fun i hi => hdvd ⟨i, hi⟩)
        · have hex_bad : ∃ i₀ : Fin m, (Finset.univ.erase i₀).gcd w' ≠ 1 := by
            by_contra hno
            exact h_sub (fun i₀ => Decidable.byContradiction fun hne => hno ⟨i₀, hne⟩)
          obtain ⟨i₀, hi₀⟩ := hex_bad
          exact lrc_nat_one_exception_sieve m (by omega) w' hw'_pos hw'_mono hw'_gcd i₀ hi₀ h_prev

end

end ReductionProofs

theorem main : H1 → H2 → H3 → type_of% @LonelyRunnerConjecture.lonely_runner_conjecture := by
  intro h1 h2 h3 n speed lonely lonely_def r
  have h_pos : ∀ (k : ℕ), 4 ≤ k → ∀ (v : Fin k → ℝ),
      (∀ i : Fin k, 0 < v i) → StrictMono v →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin k, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
    intro k hk4 v hv_pos hv_mono
    exact real_to_nat_lrc k (by omega) v hv_pos hv_mono
      (fun m hm1 _ w hw_pos hw_mono => lrc_all_nat h1 h2 h3 m hm1 w hw_pos hw_mono)
  obtain ⟨t, ht, hdist⟩ := lrc_reduction_to_pos_strictMono h_pos n speed r
  exact ⟨t, ht, (lonely_def r t).mpr hdist⟩

end OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R2
