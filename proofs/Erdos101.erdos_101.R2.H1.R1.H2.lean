import OMAReductions.R_Erdos101_erdos_101_R2_H1_R1
import Mathlib

-- Credit: @ubuwaits

/-! A linear projection of the finite homogeneous configuration preserves its collinear
triples. Quotients of the rich homotheties form a dense graph with few values. A
noncommuting pair produces a translation, whose conjugates bound the number of scales
in a large coset. Counting the original triples recovers a common scale. -/

noncomputable section

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

/- The dependent-random-choice lemmas below are selected from Adam McKenna,
LeanFormalizations.Combinatorics.Additive.BalogSzemerediGowers, commit
db02244c25aecd74eb96d9186c922387824c1258. The Apache 2.0 license follows this selection.
https://github.com/mysticflounder/lean-formalizations/blob/db02244c25aecd74eb96d9186c922387824c1258/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean
-/

namespace Finset

open scoped Pointwise

/--
**DRC step (Fox-Sudakov Lemma 5.1, "pair DRC").** For a bipartite graph
`F ⊆ X × Y` of density `c := |F| / (|X| · |Y|)` and any `0 < ε ≤ 1`, there
exists `U ⊆ X` such that
* `(c / 2) |X| ≤ |U|`, AND
* the number of ordered pairs `(x, x') ∈ U × U` with codegree
  `|N(x) ∩ N(x')| < (ε c² / 2) |Y|` is at most `ε |U|²`.

Proof (random choice): pick `v ∈ Y` uniformly and set `U := N(v) ⊆ X`. The
indicator `|U|² = (Σ_x [v ∈ N(x)])²` has expectation `≥ (E|U|)² = c² |X|²` by
Cauchy-Schwarz. For "bad" ordered pairs `(x, x')` with codegree
`< (ε c² / 2) |Y|`, the probability `P(v ∈ N(x) ∩ N(x'))` is `< ε c² / 2`, so
the expected number `Z` of bad pairs inside `U² ` is `< (ε c² / 2) |X|²`.
Hence `E[|U|² − Z/ε] ≥ (c² / 2) |X|²`, and there is a choice of `v` realizing
`|U|² ≥ (c² / 2) |X|²` (so `|U| ≥ (c / √2) |X| ≥ (c/2)|X|`) and
`Z ≤ ε |U|²`. Reference: Fox-Sudakov 2011, Lemma 5.1.
-/
lemma graph_pair_dependentRandomChoice {G : Type*} [DecidableEq G]
    (X Y : Finset G) (hX : X.Nonempty) (hY : Y.Nonempty)
    (F : Finset (G × G)) (hF_sub : F ⊆ X ×ˢ Y)
    (c : ℝ) (hc_pos : 0 < c) (_hc_le : c ≤ 1)
    (hF_dense : c * (X.card : ℝ) * (Y.card : ℝ) ≤ (F.card : ℝ))
    (ε : ℝ) (hε_pos : 0 < ε) (_hε_le : ε ≤ 1) :
    ∃ U : Finset G, U ⊆ X ∧
      (c / 2) * (X.card : ℝ) ≤ (U.card : ℝ) ∧
      (((U ×ˢ U).filter fun p : G × G ↦
        (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
          (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
        (ε * c ^ 2 / 2) * (Y.card : ℝ)).card : ℝ) ≤
      ε * (U.card : ℝ) ^ 2 := by
  have hX_real_pos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast hX.card_pos
  have hY_real_pos : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast hY.card_pos
  have hX_nn : (0 : ℝ) ≤ (X.card : ℝ) := le_of_lt hX_real_pos
  have hY_nn : (0 : ℝ) ≤ (Y.card : ℝ) := le_of_lt hY_real_pos
  -- `U(v) := { x ∈ X : (x, v) ∈ F }`.
  set U : G → Finset G := fun v ↦ X.filter (fun x ↦ (x, v) ∈ F) with hU_def
  -- "Bad" ordered pairs in `X × X` (independent of `v`).
  set Bad : Finset (G × G) := (X ×ˢ X).filter fun p : G × G ↦
    (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
      (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
    (ε * c ^ 2 / 2) * (Y.card : ℝ) with hBad_def
  -- The bad-in-U(v) finset is the restriction of `Bad` to `U(v) × U(v)`.
  set BadInV : G → Finset (G × G) := fun v ↦
    (U v ×ˢ U v).filter fun p : G × G ↦
      (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
        (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
      (ε * c ^ 2 / 2) * (Y.card : ℝ) with hBadInV_def
  -- Step 1: Σ_v |U(v)| = |F|.
  have hSum_U_card : ∑ v ∈ Y, ((U v).card : ℝ) = (F.card : ℝ) := by
    have hF_filter : F = (X ×ˢ Y).filter (fun p : G × G ↦ p ∈ F) := by
      ext p
      refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
      · exact Finset.mem_filter.mpr ⟨hF_sub hp, hp⟩
      · exact (Finset.mem_filter.mp hp).2
    have hF_card_eq : (F.card : ℝ) = ∑ v ∈ Y, ((U v).card : ℝ) := by
      conv_lhs => rw [hF_filter]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
      push_cast
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      simp only [U, Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast
      rfl
    linarith
  -- Step 2: Σ_v |U(v)|² = Σ_{(x,x') ∈ X × X} codeg(x, x').
  set codeg : G × G → ℝ := fun p : G × G ↦
    (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
      (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) with hcodeg_def
  have hcodeg_nn : ∀ p, 0 ≤ codeg p := fun p ↦ Nat.cast_nonneg _
  have hSum_U_sq : ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 = ∑ p ∈ X ×ˢ X, codeg p := by
    have hStep : ∀ v ∈ Y,
        ((U v).card : ℝ) ^ 2 = ((U v ×ˢ U v).card : ℝ) := by
      intro v _
      rw [Finset.card_product]
      push_cast; ring
    rw [Finset.sum_congr rfl hStep]
    -- Σ_v |U(v) × U(v)| = Σ_v #{(x, x') ∈ X × X : (x, v) ∈ F ∧ (x', v) ∈ F}.
    have hStep2 : ∀ v ∈ Y, ((U v ×ˢ U v).card : ℝ) =
        (((X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F)).card : ℝ) := by
      intro v _
      have hSet : U v ×ˢ U v =
          (X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F) := by
        ext p
        simp only [Finset.mem_product, Finset.mem_filter, U]
        tauto
      rw [hSet]
    rw [Finset.sum_congr rfl hStep2]
    -- Swap sums: Σ_v #{(x,x'): (x,v)∈F ∧ (x',v)∈F} = Σ_{(x,x')} codeg(x,x').
    rw [show (∑ v ∈ Y,
        (((X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F)).card : ℝ)) =
        ∑ v ∈ Y, ∑ p ∈ X ×ˢ X,
          (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) from by
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast; rfl]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    -- codeg(p) = #{v ∈ Y : (p.1, v) ∈ F ∧ (p.2, v) ∈ F}.
    have hcodeg_eq : codeg p =
        ∑ v ∈ Y, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
      simp only [codeg]
      rw [show (Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩ (Y.filter (fun y ↦ (p.2, y) ∈ F))
          = Y.filter (fun y ↦ (p.1, y) ∈ F ∧ (p.2, y) ∈ F) from by
        ext y; simp only [Finset.mem_inter, Finset.mem_filter]; tauto]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast; rfl
    rw [hcodeg_eq]
  -- Step 3: Cauchy-Schwarz: |F|² ≤ |Y| · Σ_v |U(v)|².
  have hCS : (F.card : ℝ) ^ 2 ≤ (Y.card : ℝ) * ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Y (fun _ : G ↦ (1 : ℝ))
      (fun v ↦ ((U v).card : ℝ))
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [hSum_U_card] at h
    exact h
  -- Step 4: c²|X|²|Y| ≤ Σ_v |U(v)|².
  have hSum_U_sq_lb : c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤
      ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 := by
    have hc_nn : 0 ≤ c := le_of_lt hc_pos
    have hF_dense_nn : 0 ≤ c * (X.card : ℝ) * (Y.card : ℝ) :=
      mul_nonneg (mul_nonneg hc_nn hX_nn) hY_nn
    have hF_sq : (c * (X.card : ℝ) * (Y.card : ℝ)) ^ 2 ≤ (F.card : ℝ) ^ 2 :=
      pow_le_pow_left₀ hF_dense_nn hF_dense 2
    have hY_pos : 0 < (Y.card : ℝ) := hY_real_pos
    have h := le_trans hF_sq hCS
    have hrw : (c * (X.card : ℝ) * (Y.card : ℝ)) ^ 2 =
        (Y.card : ℝ) * (c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) := by ring
    rw [hrw] at h
    exact le_of_mul_le_mul_left h hY_pos
  -- Step 5: Σ_v |BadInV(v)| ≤ (ε c² / 2) |X|² |Y|.
  -- For each bad pair (x, x'), the number of v ∈ Y with x, x' ∈ U(v) equals
  -- codeg(x, x') ≤ (ε c² / 2)|Y|.
  have hSum_BadInV_le : ∑ v ∈ Y, ((BadInV v).card : ℝ) ≤
      (ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by
    -- Σ_v |BadInV(v)| = Σ_{p ∈ Bad} codeg(p).
    have hSwap : ∑ v ∈ Y, ((BadInV v).card : ℝ) = ∑ p ∈ Bad, codeg p := by
      -- Σ_v #{(x,x') ∈ U(v)² : p ∈ Bad}.
      have hStep : ∀ v ∈ Y, ((BadInV v).card : ℝ) =
          ∑ p ∈ Bad, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
        intro v _
        -- BadInV(v) = Bad.filter (p ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F).
        have hBadInV_eq : BadInV v =
            Bad.filter (fun p ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F) := by
          ext p
          simp only [BadInV, Bad, Finset.mem_filter, Finset.mem_product, U,
            Finset.mem_filter]
          tauto
        rw [hBadInV_eq, Finset.card_eq_sum_ones, Finset.sum_filter]
        push_cast; rfl
      rw [Finset.sum_congr rfl hStep]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      have hcodeg_eq : codeg p =
          ∑ v ∈ Y, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
        simp only [codeg]
        rw [show (Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩ (Y.filter (fun y ↦ (p.2, y) ∈ F))
            = Y.filter (fun y ↦ (p.1, y) ∈ F ∧ (p.2, y) ∈ F) from by
          ext y; simp only [Finset.mem_inter, Finset.mem_filter]; tauto]
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        push_cast; rfl
      rw [hcodeg_eq]
    rw [hSwap]
    -- Σ_{p ∈ Bad} codeg(p) ≤ |Bad| · (εc²/2)|Y| ≤ |X|² · (εc²/2)|Y|.
    have hBad_sub : Bad ⊆ X ×ˢ X := Finset.filter_subset _ _
    have hBad_card_le : (Bad.card : ℝ) ≤ ((X ×ˢ X).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hBad_sub
    have hXX_card : ((X ×ˢ X).card : ℝ) = (X.card : ℝ) ^ 2 := by
      rw [Finset.card_product]; push_cast; ring
    have hBad_card_le_X_sq : (Bad.card : ℝ) ≤ (X.card : ℝ) ^ 2 := by
      rw [← hXX_card]; exact hBad_card_le
    have hτ_nn : 0 ≤ (ε * c ^ 2 / 2) * (Y.card : ℝ) := by positivity
    have hPointwise : ∀ p ∈ Bad, codeg p ≤ (ε * c ^ 2 / 2) * (Y.card : ℝ) := by
      intro p hp
      simp only [Bad, Finset.mem_filter] at hp
      exact le_of_lt hp.2
    calc ∑ p ∈ Bad, codeg p
        ≤ ∑ _p ∈ Bad, (ε * c ^ 2 / 2) * (Y.card : ℝ) :=
          Finset.sum_le_sum hPointwise
      _ = (Bad.card : ℝ) * ((ε * c ^ 2 / 2) * (Y.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (X.card : ℝ) ^ 2 * ((ε * c ^ 2 / 2) * (Y.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hBad_card_le_X_sq hτ_nn
      _ = (ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by ring
  -- Step 6: Σ_v Φ(v) ≥ (c² / 2) |X|² |Y|, where Φ(v) = |U(v)|² − (1/ε) |BadInV(v)|.
  set Φ : G → ℝ := fun v ↦
    ((U v).card : ℝ) ^ 2 - (1 / ε) * ((BadInV v).card : ℝ) with hΦ_def
  have hε_inv_pos : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε_pos
  have hε_inv_nn : (0 : ℝ) ≤ 1 / ε := le_of_lt hε_inv_pos
  have hSum_Φ_lb : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤ ∑ v ∈ Y, Φ v := by
    have hSplit : ∑ v ∈ Y, Φ v =
        (∑ v ∈ Y, ((U v).card : ℝ) ^ 2) - (1 / ε) * ∑ v ∈ Y, ((BadInV v).card : ℝ) := by
      simp only [Φ]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hSplit]
    have h1 : c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤ ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 :=
      hSum_U_sq_lb
    have h2 : (1 / ε) * ∑ v ∈ Y, ((BadInV v).card : ℝ) ≤
        (1 / ε) * ((ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hSum_BadInV_le hε_inv_nn
    have h2' : (1 / ε) * ((ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) =
        (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by
      field_simp
    rw [h2'] at h2
    linarith
  -- Step 7: Extract a `v` with Φ(v) ≥ (c²/2)|X|².
  have hSum_Φ_const : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) =
      ∑ _v ∈ Y, (c ^ 2 / 2) * (X.card : ℝ) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hSum_Φ_const] at hSum_Φ_lb
  obtain ⟨v, _hvY, hΦv⟩ := Finset.exists_le_of_sum_le hY hSum_Φ_lb
  -- Step 8: For this `v`, derive |U(v)| ≥ (c/2)|X| and |BadInV(v)| ≤ ε|U(v)|².
  -- From hΦv : (c²/2)|X|² ≤ |U(v)|² - (1/ε)|BadInV(v)|.
  -- Since |BadInV(v)| ≥ 0, |U(v)|² ≥ (c²/2)|X|² ≥ (c/2)²|X|² (because c ≤ 1).
  have hU_card_nn : (0 : ℝ) ≤ ((U v).card : ℝ) := Nat.cast_nonneg _
  have hBadInV_nn : (0 : ℝ) ≤ ((BadInV v).card : ℝ) := Nat.cast_nonneg _
  have hU_sq_lb : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 ≤ ((U v).card : ℝ) ^ 2 := by
    have h1 : (1 / ε) * ((BadInV v).card : ℝ) ≥ 0 :=
      mul_nonneg hε_inv_nn hBadInV_nn
    linarith
  have hc_sq_half_ge_c_half_sq : (c / 2) ^ 2 ≤ c ^ 2 / 2 := by
    have hc_nn : 0 ≤ c := le_of_lt hc_pos
    have : (c / 2) ^ 2 = c ^ 2 / 4 := by ring
    rw [this]
    -- c²/4 ≤ c²/2 ↔ c² ≥ 0.
    nlinarith [sq_nonneg c]
  have hU_card_lb : (c / 2) * (X.card : ℝ) ≤ ((U v).card : ℝ) := by
    have hc_half_X_nn : (0 : ℝ) ≤ (c / 2) * (X.card : ℝ) :=
      mul_nonneg (by linarith) hX_nn
    have hsq_chain : ((c / 2) * (X.card : ℝ)) ^ 2 ≤ ((U v).card : ℝ) ^ 2 := by
      calc ((c / 2) * (X.card : ℝ)) ^ 2
          = (c / 2) ^ 2 * (X.card : ℝ) ^ 2 := by ring
        _ ≤ (c ^ 2 / 2) * (X.card : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hc_sq_half_ge_c_half_sq (sq_nonneg _)
        _ ≤ ((U v).card : ℝ) ^ 2 := hU_sq_lb
    have hsqrt := Real.sqrt_le_sqrt hsq_chain
    rwa [Real.sqrt_sq hc_half_X_nn, Real.sqrt_sq hU_card_nn] at hsqrt
  -- |BadInV(v)| ≤ ε |U(v)|².
  have hBadInV_le : ((BadInV v).card : ℝ) ≤ ε * ((U v).card : ℝ) ^ 2 := by
    -- From hΦv: (c²/2)|X|² ≤ |U(v)|² − (1/ε)|BadInV(v)|.
    -- So (1/ε)|BadInV(v)| ≤ |U(v)|² − (c²/2)|X|² ≤ |U(v)|².
    have h1 : (1 / ε) * ((BadInV v).card : ℝ) ≤ ((U v).card : ℝ) ^ 2 := by
      have hX_sq_nn : 0 ≤ (c ^ 2 / 2) * (X.card : ℝ) ^ 2 := by positivity
      linarith
    have h2 : ((BadInV v).card : ℝ) ≤ ε * ((U v).card : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hε_pos)
      have heq : ε * ((1 / ε) * ((BadInV v).card : ℝ)) = ((BadInV v).card : ℝ) := by
        field_simp
      rw [heq] at this
      exact this
    exact h2
  -- Step 9: Package the witness.
  refine ⟨U v, ?_, hU_card_lb, ?_⟩
  · simp only [U]; exact Finset.filter_subset _ _
  · exact hBadInV_le

/--
**High-degree subset density.** For `E ⊆ A ×ˢ B` with `|A| = |B| = n` and
`δ n² ≤ |E|`, the subset `A₁ := { a ∈ A : (δ/2) n ≤ |Nb(a)| }` has
`(δ/2) n ≤ |A₁|` and `e(A₁, B) ≥ (δ/2) n²` (where `e(A₁, B) := |E ∩ (A₁ ×ˢ B)|`).

Standard rare/popular split: rows with `|Nb(a)| < (δ/2) n` contribute
`< (δ/2) n²` edges, so the popular rows in `A₁` contribute `≥ (δ/2) n²`.
Combined with the pointwise bound `|Nb(a)| ≤ n` on `A₁`, this gives
`|A₁| · n ≥ (δ/2) n²`, i.e. `|A₁| ≥ (δ/2) n`.
-/
lemma graph_high_degree_subset_lb {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    (δ / 2) * (A.card : ℝ) ≤
      ((A.filter (fun a ↦
        (δ / 2) * (B.card : ℝ) ≤
          ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ))).card : ℝ) ∧
    (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤
      ((E.filter (fun p : G × G ↦
        (δ / 2) * (B.card : ℝ) ≤
          ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ))).card : ℝ) := by
  classical
  set rowDeg : G → ℕ := fun a ↦ (B.filter (fun b ↦ (a, b) ∈ E)).card with hrowDeg_def
  set Apop : Finset G := A.filter (fun a ↦ (δ / 2) * (B.card : ℝ) ≤ (rowDeg a : ℝ))
    with hApop_def
  set Epop : Finset (G × G) := E.filter (fun p : G × G ↦
    (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ))
    with hEpop_def
  have hApop_sub : Apop ⊆ A := Finset.filter_subset _ _
  have hEpop_sub : Epop ⊆ E := Finset.filter_subset _ _
  have hA_pos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hA_nn : (0 : ℝ) ≤ (A.card : ℝ) := le_of_lt hA_pos
  have hBcard_eq : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hAB.symm
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := by rw [hBcard_eq]; exact hA_pos
  have hB_nn : (0 : ℝ) ≤ (B.card : ℝ) := le_of_lt hB_pos
  have hrowDeg_le : ∀ a, rowDeg a ≤ B.card := fun a ↦
    Finset.card_le_card (Finset.filter_subset _ _)
  have hrowDeg_le_R : ∀ a, (rowDeg a : ℝ) ≤ (B.card : ℝ) := fun a ↦ by
    exact_mod_cast hrowDeg_le a
  have hSumRow : ∑ a ∈ A, (rowDeg a : ℕ) = E.card := by
    have step1 : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have step2 : ∑ a ∈ A, rowDeg a = ∑ p ∈ A ×ˢ B, (if p ∈ E then 1 else 0) := by
      simp_rw [step1, Finset.sum_product]
    have step3 :
        ∑ p ∈ A ×ˢ B, (if p ∈ E then 1 else 0) = ((A ×ˢ B).filter (· ∈ E)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have step4 : (A ×ˢ B).filter (· ∈ E) = E := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hE_sub h, h⟩⟩
    rw [step2, step3, step4]
  have hSumRow_real : ∑ a ∈ A, (rowDeg a : ℝ) = (E.card : ℝ) := by
    have h := hSumRow
    have hcast : ((∑ a ∈ A, rowDeg a : ℕ) : ℝ) = (E.card : ℝ) := by exact_mod_cast h
    push_cast at hcast; exact hcast
  have hsplit_A : ∑ a ∈ A, (rowDeg a : ℝ) =
      (∑ a ∈ Apop, (rowDeg a : ℝ)) + ∑ a ∈ A \ Apop, (rowDeg a : ℝ) := by
    rw [← Finset.sum_sdiff hApop_sub]; ring
  have hrare : ∑ a ∈ A \ Apop, (rowDeg a : ℝ) ≤
      ((A \ Apop).card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
    rw [show ((A \ Apop).card : ℝ) * ((δ / 2) * (B.card : ℝ)) =
              ∑ _a ∈ A \ Apop, ((δ / 2) * (B.card : ℝ)) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a ha ↦ ?_
    rw [Finset.mem_sdiff, hApop_def, Finset.mem_filter] at ha
    have hnot := ha.2
    by_contra hgt
    push Not at hgt
    exact hnot ⟨ha.1, le_of_lt hgt⟩
  have hAdiff_le_A : ((A \ Apop).card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := A) (t := Apop))
  have hδ2B_nn : 0 ≤ (δ / 2) * (B.card : ℝ) := by positivity
  have hrare' : ∑ a ∈ A \ Apop, (rowDeg a : ℝ) ≤ (A.card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hAdiff_le_A hδ2B_nn
    linarith [hrare]
  have hSumApop : ∑ a ∈ Apop, (rowDeg a : ℕ) = Epop.card := by
    have step1 : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have step2 : ∑ a ∈ Apop, rowDeg a = ∑ p ∈ Apop ×ˢ B, (if p ∈ E then 1 else 0) := by
      simp_rw [step1, Finset.sum_product]
    have step3 : ∑ p ∈ Apop ×ˢ B, (if p ∈ E then 1 else 0) =
        ((Apop ×ˢ B).filter (· ∈ E)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have step4 : (Apop ×ˢ B).filter (· ∈ E) = Epop := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, hEpop_def, hApop_def, hrowDeg_def]
      constructor
      · rintro ⟨⟨⟨hp1A, hp1pop⟩, _hp2⟩, hpE⟩
        exact ⟨hpE, hp1pop⟩
      · rintro ⟨hpE, hpop⟩
        have hpAB := hE_sub hpE
        rw [Finset.mem_product] at hpAB
        exact ⟨⟨⟨hpAB.1, hpop⟩, hpAB.2⟩, hpE⟩
    rw [step2, step3, step4]
  have hSumApop_real : ∑ a ∈ Apop, (rowDeg a : ℝ) = (Epop.card : ℝ) := by
    have h := hSumApop
    have hcast : ((∑ a ∈ Apop, rowDeg a : ℕ) : ℝ) = (Epop.card : ℝ) := by exact_mod_cast h
    push_cast at hcast; exact hcast
  have hE_dense' : δ * (A.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ A, (rowDeg a : ℝ) := by
    rw [hSumRow_real]; exact hE_dense
  have hEpop_lb : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (Epop.card : ℝ) := by
    have : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ Apop, (rowDeg a : ℝ) := by
      have hδ_split : δ * (A.card : ℝ) * (B.card : ℝ) =
          (δ / 2) * (A.card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
        ring
      linarith [hE_dense', hsplit_A, hrare', hδ_split]
    linarith [this, hSumApop_real]
  have hApop_sum_ub : ∑ a ∈ Apop, (rowDeg a : ℝ) ≤ (Apop.card : ℝ) * (B.card : ℝ) := by
    rw [show (Apop.card : ℝ) * (B.card : ℝ) = ∑ _a ∈ Apop, (B.card : ℝ) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a _ ↦ hrowDeg_le_R a
  have hApop_lb : (δ / 2) * (A.card : ℝ) ≤ (Apop.card : ℝ) := by
    have h1 : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (Apop.card : ℝ) * (B.card : ℝ) := by
      calc (δ / 2) * (A.card : ℝ) * (B.card : ℝ)
          ≤ (Epop.card : ℝ) := hEpop_lb
        _ = ∑ a ∈ Apop, (rowDeg a : ℝ) := hSumApop_real.symm
        _ ≤ (Apop.card : ℝ) * (B.card : ℝ) := hApop_sum_ub
    exact le_of_mul_le_mul_right h1 hB_pos
  exact ⟨hApop_lb, hEpop_lb⟩

/--
**Markov refinement helper.** Given `U` and a bad-pair count bound
`#{(a, a') ∈ U×U : codeg_E(a, a') < τ} ≤ κ · |U|²`, produce
`A' ⊆ U` with `|A'| ≥ |U|/2` (when `κ ≤ 1/4`) such that for every
`a ∈ A'` the bad-partner count `#{a' ∈ U : codeg_E(a, a') < τ}` is
`≤ 2κ · |U|`.  Used inside `graph_dependentRandomChoice_payoff_pointwise_witness` with
`κ := δ/16`, giving `2κ = δ/8`.
-/
private lemma graph_dependentRandomChoice_markov_refinement {G : Type*} [DecidableEq G]
    (B U : Finset G) (E : Finset (G × G)) (τ : ℝ) (κ : ℝ)
    (hκ_pos : 0 < κ) (hUpos : (0 : ℝ) < (U.card : ℝ))
    (hbadCount : (((U ×ˢ U).filter fun p : G × G ↦
        ((B.filter fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
      ≤ κ * (U.card : ℝ) ^ 2) :
    ∃ A' : Finset G, A' ⊆ U ∧
      (1 - 1 / 2) * (U.card : ℝ) ≤ (A'.card : ℝ) ∧
      (∀ a ∈ A',
        ((U.filter fun a₁ ↦
          ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
          ≤ 2 * κ * (U.card : ℝ)) := by
  classical
  -- Bad partners of `a` in U.
  set badPartner : G → Finset G := fun a ↦
    U.filter (fun a₁ ↦
      ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) < τ)
    with hbadPartner_def
  set A' : Finset G := U.filter (fun a ↦
    ((badPartner a).card : ℝ) ≤ 2 * κ * (U.card : ℝ)) with hA'_def
  have hA'_sub : A' ⊆ U := Finset.filter_subset _ _
  -- Sum of bad-partner cards equals bad-pair count (fiber over first coord).
  set badPairs : Finset (G × G) := (U ×ˢ U).filter (fun p : G × G ↦
    ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ)
    with hbadPairs_def
  have hbadSum : (badPairs.card : ℝ) = ∑ a ∈ U, ((badPartner a).card : ℝ) := by
    have hN : badPairs.card = ∑ a ∈ U, (badPartner a).card := by
      rw [hbadPairs_def, hbadPartner_def]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcast : ((∑ a ∈ U, (badPartner a).card : ℕ) : ℝ) = (badPairs.card : ℝ) := by
      exact_mod_cast hN.symm
    push_cast at hcast; linarith
  -- Markov lower bound on Σ over U \ A'.
  have hsum_split :
      ∑ a ∈ U, ((badPartner a).card : ℝ) =
        (∑ a ∈ A', ((badPartner a).card : ℝ)) +
        ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := by
    rw [← Finset.sum_sdiff hA'_sub]; ring
  have hsum_diff_ge :
      ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) ≤
        ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := by
    rw [show ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) =
            ∑ _a ∈ U \ A', (2 * κ * (U.card : ℝ)) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a ha ↦ ?_
    rw [Finset.mem_sdiff, hA'_def, Finset.mem_filter] at ha
    have hnot := ha.2
    by_contra hge
    push Not at hge
    exact hnot ⟨ha.1, le_of_lt hge⟩
  have hpartner_nn : ∀ a, 0 ≤ ((badPartner a).card : ℝ) := fun a ↦ Nat.cast_nonneg _
  have hsum_A'_nn : 0 ≤ ∑ a ∈ A', ((badPartner a).card : ℝ) :=
    Finset.sum_nonneg fun a _ ↦ hpartner_nn a
  -- Combine: |U\A'| · 2κ|U| ≤ Σ over U ≤ |badPairs| ≤ κ|U|².  Hence |U\A'| ≤ |U|/2.
  have hdiff_card_le : ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) ≤
      κ * (U.card : ℝ) ^ 2 := by
    calc ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ))
        ≤ ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := hsum_diff_ge
      _ ≤ ∑ a ∈ U, ((badPartner a).card : ℝ) := by linarith
      _ = (badPairs.card : ℝ) := hbadSum.symm
      _ ≤ κ * (U.card : ℝ) ^ 2 := hbadCount
  have hcoeff_pos : 0 < 2 * κ * (U.card : ℝ) := by positivity
  have hdiff_le_half : ((U \ A').card : ℝ) ≤ (U.card : ℝ) / 2 := by
    have heq : κ * (U.card : ℝ) ^ 2 = ((U.card : ℝ) / 2) * (2 * κ * (U.card : ℝ)) := by ring
    rw [heq] at hdiff_card_le
    exact le_of_mul_le_mul_right hdiff_card_le hcoeff_pos
  have hA'_card_real : ((U \ A').card : ℝ) + (A'.card : ℝ) = (U.card : ℝ) := by
    have h : (U \ A').card + A'.card = U.card := Finset.card_sdiff_add_card_eq_card hA'_sub
    exact_mod_cast h
  have hA'_lb : (U.card : ℝ) / 2 ≤ (A'.card : ℝ) := by linarith
  refine ⟨A', hA'_sub, ?_, ?_⟩
  · linarith
  · intro a ha
    rw [hA'_def, Finset.mem_filter] at ha
    exact ha.2

/--
**Popular columns helper.** For `U ⊆ A` with row degree `≥ ρ · |B|` for every
`a ∈ U` (in the sense of `|{b ∈ B : (a, b) ∈ E}| ≥ ρ · |B|`), the rare/popular
split on columns produces `B' ⊆ B` of cardinality `≥ (ρ/2) · |B|` such that
every `b ∈ B'` has `|{a ∈ U : (a, b) ∈ E}| ≥ (ρ/2) · |U|`.
-/
private lemma graph_dependentRandomChoice_popular_columns {G : Type*} [DecidableEq G]
    (A B : Finset G) (hAB : A.card = B.card)
    (E : Finset (G × G)) (_hE_sub : E ⊆ A ×ˢ B)
    (U : Finset G) (hU_sub : U ⊆ A)
    (hU_pos : (0 : ℝ) < (U.card : ℝ))
    (ρ : ℝ) (hρ_pos : 0 < ρ) (_hρ_le_one : ρ ≤ 1)
    (hrowDeg_lb : ∀ a ∈ U, ρ * (B.card : ℝ) ≤
      ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ)) :
    ∃ B' : Finset G, B' ⊆ B ∧
      (ρ / 2) * (B.card : ℝ) ≤ (B'.card : ℝ) ∧
      (∀ b ∈ B', (ρ / 2) * (U.card : ℝ) ≤
        ((U.filter fun a ↦ (a, b) ∈ E).card : ℝ)) := by
  classical
  -- |B| > 0 since |B| = |A| and U ⊆ A nonempty.
  have hBcard_nat : B.card = A.card := hAB.symm
  have hUcard_le_A : (U.card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hU_sub
  have hA_pos : (0 : ℝ) < (A.card : ℝ) := lt_of_lt_of_le hU_pos hUcard_le_A
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := by
    have : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hBcard_nat
    rw [this]; exact hA_pos
  -- Column count.
  set colCount : G → ℕ := fun b ↦ (U.filter (fun a ↦ (a, b) ∈ E)).card with hcolCount_def
  set B' : Finset G := B.filter (fun b ↦ (ρ / 2) * (U.card : ℝ) ≤ (colCount b : ℝ)) with hB'_def
  have hB'_sub : B' ⊆ B := Finset.filter_subset _ _
  -- Edge count from U: Σ_a∈U rowDeg(a) ≥ ρ|U||B|.  Also = Σ_b colCount b.
  set rowDeg : G → ℕ := fun a ↦ (B.filter (fun b ↦ (a, b) ∈ E)).card with hrowDeg_def
  -- Σ over U of rowDeg = Σ over B of colCount: both count {(a, b) ∈ U × B : (a, b) ∈ E}.
  have hSwap : ∑ a ∈ U, (rowDeg a : ℕ) = ∑ b ∈ B, (colCount b : ℕ) := by
    have hrowDeg_eq : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcolCount_eq : ∀ b, colCount b = ∑ a ∈ U, (if (a, b) ∈ E then 1 else 0) := fun b ↦ by
      simp only [colCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [hrowDeg_eq, hcolCount_eq]
    rw [Finset.sum_comm]
  have hSwap_real :
      ∑ a ∈ U, (rowDeg a : ℝ) = ∑ b ∈ B, (colCount b : ℝ) := by
    have : ((∑ a ∈ U, rowDeg a : ℕ) : ℝ) = ((∑ b ∈ B, colCount b : ℕ) : ℝ) := by
      exact_mod_cast hSwap
    push_cast at this; exact this
  -- Σ_{a ∈ U} rowDeg(a) ≥ ρ|U||B|.
  have hrow_sum_lb : ρ * (U.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ U, (rowDeg a : ℝ) := by
    have hsum : ∑ _a ∈ U, ρ * (B.card : ℝ) ≤ ∑ a ∈ U, (rowDeg a : ℝ) :=
      Finset.sum_le_sum fun a haU ↦ hrowDeg_lb a haU
    have hconst : ∑ _a ∈ U, ρ * (B.card : ℝ) = (U.card : ℝ) * (ρ * (B.card : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst] at hsum
    linarith
  have hcol_sum_lb : ρ * (U.card : ℝ) * (B.card : ℝ) ≤ ∑ b ∈ B, (colCount b : ℝ) := by
    rw [← hSwap_real]; exact hrow_sum_lb
  -- Rare columns contribute < (ρ/2)|U| each.
  have hrare_col : ∑ b ∈ B \ B', (colCount b : ℝ) ≤
      ((B \ B').card : ℝ) * ((ρ / 2) * (U.card : ℝ)) := by
    rw [show ((B \ B').card : ℝ) * ((ρ / 2) * (U.card : ℝ)) =
            ∑ _b ∈ B \ B', ((ρ / 2) * (U.card : ℝ)) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun b hb ↦ ?_
    rw [Finset.mem_sdiff, hB'_def, Finset.mem_filter] at hb
    have hnot := hb.2
    by_contra hgt
    push Not at hgt
    exact hnot ⟨hb.1, le_of_lt hgt⟩
  have hrare_col' : ∑ b ∈ B \ B', (colCount b : ℝ) ≤
      (B.card : ℝ) * ((ρ / 2) * (U.card : ℝ)) := by
    have h : ((B \ B').card : ℝ) ≤ (B.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := B) (t := B'))
    have hnn : 0 ≤ (ρ / 2) * (U.card : ℝ) := by
      have : 0 ≤ ρ / 2 := by linarith
      exact mul_nonneg this (le_of_lt hU_pos)
    have := mul_le_mul_of_nonneg_right h hnn
    linarith
  -- Split column-sum.
  have hcol_split : ∑ b ∈ B, (colCount b : ℝ) =
      (∑ b ∈ B', (colCount b : ℝ)) + ∑ b ∈ B \ B', (colCount b : ℝ) := by
    rw [← Finset.sum_sdiff hB'_sub]; ring
  have hpop_col_lb : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) ≤
      ∑ b ∈ B', (colCount b : ℝ) := by
    nlinarith [hcol_split, hcol_sum_lb, hrare_col']
  -- Σ over B' of colCount ≤ |B'| · |U|.
  have hcolCount_le : ∀ b, (colCount b : ℝ) ≤ (U.card : ℝ) := fun b ↦ by
    have h : (colCount b : ℕ) ≤ U.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    exact_mod_cast h
  have hpop_col_ub : ∑ b ∈ B', (colCount b : ℝ) ≤ (B'.card : ℝ) * (U.card : ℝ) := by
    rw [show (B'.card : ℝ) * (U.card : ℝ) = ∑ _b ∈ B', (U.card : ℝ) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    exact Finset.sum_le_sum fun b _ ↦ hcolCount_le b
  -- Divide through by |U|.
  have hB'_lb : (ρ / 2) * (B.card : ℝ) ≤ (B'.card : ℝ) := by
    have hchain : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) ≤
        (B'.card : ℝ) * (U.card : ℝ) := le_trans hpop_col_lb hpop_col_ub
    have hrew : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) =
        ((ρ / 2) * (B.card : ℝ)) * (U.card : ℝ) := by ring
    rw [hrew] at hchain
    exact le_of_mul_le_mul_right hchain hU_pos
  have hpop_col_prop : ∀ b ∈ B', (ρ / 2) * (U.card : ℝ) ≤ (colCount b : ℝ) := by
    intro b hb
    rw [hB'_def, Finset.mem_filter] at hb
    exact hb.2
  exact ⟨B', hB'_sub, hB'_lb, hpop_col_prop⟩

/--
**Witness for the DRC pointwise payoff (steps 1-4).** Internal helper.
Composes `graph_high_degree_subset_lb` (rare/popular row split) with
`graph_pair_dependentRandomChoice` (Fox-Sudakov 5.1 pair-DRC) and a Markov + rare/popular
column split.  Returns the four pieces needed by the pointwise count
step: a "core" set `U ⊆ A`, the "non-bad" refinement `A' ⊆ U`, the
"popular column" refinement `B' ⊆ B`, and the codegree threshold
`τ ≥ 0` that interpolates the bad-partner bound for `a ∈ A'` and the
final `(δ⁵/2¹²)|A|²` count.

The arithmetic identity `(δ⁵/2¹²)|A|² ≤ (δ/8)|U| · τ` is established
here (using `m := |Apop|`-relative density and `|U| · τ`-style
cancellation) so the count helper need not redo it.
-/
private lemma graph_dependentRandomChoice_payoff_pointwise_witness {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ U A' B' : Finset G, ∃ τ : ℝ,
      U ⊆ A ∧ A' ⊆ U ∧ B' ⊆ B ∧
      0 ≤ τ ∧
      (δ / 4) * (A.card : ℝ) ≤ (U.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ ∧
      (∀ a ∈ A',
        ((U.filter fun a₁ ↦
          ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
          ≤ (δ / 8) * (U.card : ℝ)) ∧
      (∀ b ∈ B',
        (δ / 4) * (U.card : ℝ) ≤
          ((U.filter fun a₁ ↦ (a₁, b) ∈ E).card : ℝ)) := by
  classical
  -- Cardinality positivity.
  have hApos : 0 < A.card := hA.card_pos
  have hA_real_pos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hApos
  have hA_nn : (0 : ℝ) ≤ (A.card : ℝ) := le_of_lt hA_real_pos
  have hBcard_nat : B.card = A.card := hAB.symm
  have hB_real_eq : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hBcard_nat
  have hB_real_pos : (0 : ℝ) < (B.card : ℝ) := by rw [hB_real_eq]; exact hA_real_pos
  have hB : B.Nonempty := by
    rw [← Finset.card_pos]; rw [hBcard_nat]; exact hApos
  -- δ bounds.
  have hδ_nn : 0 ≤ δ := le_of_lt hδ_pos
  -- Step 1: apply rare/popular row split.
  obtain ⟨hApop_lb, hEpop_lb⟩ :=
    graph_high_degree_subset_lb δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense
  -- Define A₁ (popular rows) and E₁ (edges with popular first coord).
  set A₁ : Finset G := A.filter (fun a ↦
    (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ)) with hA₁_def
  have hA₁_sub : A₁ ⊆ A := Finset.filter_subset _ _
  -- |A₁| ≥ (δ/2)|A| > 0, so A₁ is nonempty.
  have hA₁_card_pos : (0 : ℝ) < (A₁.card : ℝ) := by
    have : 0 < (δ / 2) * (A.card : ℝ) := by positivity
    linarith
  have hA₁_card_pos_nat : 0 < A₁.card := by exact_mod_cast hA₁_card_pos
  have hA₁_ne : A₁.Nonempty := Finset.card_pos.mp hA₁_card_pos_nat
  set E₁ : Finset (G × G) := E.filter (fun p ↦ p.1 ∈ A₁) with hE₁_def
  have hE₁_sub_E : E₁ ⊆ E := Finset.filter_subset _ _
  -- E₁ characterisation: edges with first coord in A₁.
  have hE₁_iff : ∀ p, p ∈ E₁ ↔ p ∈ E ∧ p.1 ∈ A₁ := fun p ↦ by
    simp [E₁, Finset.mem_filter]
  -- E₁ ⊆ A₁ ×ˢ B.
  have hE₁_sub : E₁ ⊆ A₁ ×ˢ B := by
    intro p hp
    rw [hE₁_iff] at hp
    obtain ⟨hpE, hpA₁⟩ := hp
    have hpAB := hE_sub hpE
    rw [Finset.mem_product] at hpAB ⊢
    exact ⟨hpA₁, hpAB.2⟩
  -- The edge count for E₁: this matches the popular-edge form of `graph_high_degree_subset_lb`.
  -- |E₁| = |E.filter (popular first coord)| ≥ (δ/2)·|A|·|B|.
  have hE₁_card_lb : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (E₁.card : ℝ) := by
    -- The popular-edge filter from `graph_high_degree_subset_lb` matches E₁:
    --   E.filter (popular p.1) = E.filter (p.1 ∈ A₁)
    have hfilter_eq :
        E.filter (fun p : G × G ↦
          (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ)) = E₁ := by
      ext p
      simp only [E₁, Finset.mem_filter, hA₁_def]
      constructor
      · rintro ⟨hpE, hpop⟩
        have hpAB := hE_sub hpE
        rw [Finset.mem_product] at hpAB
        exact ⟨hpE, hpAB.1, hpop⟩
      · rintro ⟨hpE, _, hpop⟩
        exact ⟨hpE, hpop⟩
    rw [← hfilter_eq]; exact hEpop_lb
  -- Step 2: invoke graph_pair_dependentRandomChoice on (A₁, B, E₁) with density c₀ = (δ/2)|A|/|A₁|.
  set m : ℝ := (A₁.card : ℝ) with hm_def
  have hm_pos : 0 < m := hA₁_card_pos
  have hm_le_A : m ≤ (A.card : ℝ) := by
    have : (A₁.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hA₁_sub
    exact this
  -- Density c₀ for pair-DRC: c₀ * m * |B| = (δ/2) * |A| * |B|.
  set c₀ : ℝ := (δ / 2) * (A.card : ℝ) / m with hc₀_def
  have hc₀_pos : 0 < c₀ := by
    have hnum : 0 < (δ / 2) * (A.card : ℝ) := by positivity
    exact div_pos hnum hm_pos
  -- c₀ ≤ 1, because (δ/2)|A| ≤ m (= |A₁|).
  have hc₀_le_one : c₀ ≤ 1 := by
    rw [hc₀_def]
    rw [div_le_one hm_pos]
    exact hApop_lb
  -- c₀ * |A₁| = (δ/2) * |A|.
  have hc₀_mul_m : c₀ * m = (δ / 2) * (A.card : ℝ) := by
    rw [hc₀_def]; field_simp
  -- Density hypothesis for graph_pair_dependentRandomChoice.
  have hF_dense_drc : c₀ * (A₁.card : ℝ) * (B.card : ℝ) ≤ (E₁.card : ℝ) := by
    have : c₀ * (A₁.card : ℝ) * (B.card : ℝ) = (δ / 2) * (A.card : ℝ) * (B.card : ℝ) := by
      rw [show (A₁.card : ℝ) = m from rfl]; rw [hc₀_mul_m]
    rw [this]; exact hE₁_card_lb
  -- ε = δ/16.
  set ε : ℝ := δ / 16 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; positivity
  have hε_le_one : ε ≤ 1 := by
    rw [hε_def]; linarith
  -- Invoke graph_pair_dependentRandomChoice.
  obtain ⟨U, hU_sub_A₁, hU_card_lb_drc, hbad_card_le⟩ :=
    graph_pair_dependentRandomChoice A₁ B hA₁_ne hB E₁ hE₁_sub c₀ hc₀_pos hc₀_le_one hF_dense_drc
      ε hε_pos hε_le_one
  have hU_sub : U ⊆ A := hU_sub_A₁.trans hA₁_sub
  -- (c₀/2) * |A₁| = (δ/4) * |A|.
  have hU_card_lb : (δ / 4) * (A.card : ℝ) ≤ (U.card : ℝ) := by
    have heq : c₀ / 2 * (A₁.card : ℝ) = (δ / 4) * (A.card : ℝ) := by
      have := hc₀_mul_m
      rw [show (A₁.card : ℝ) = m from rfl]
      linarith
    linarith [hU_card_lb_drc, heq]
  have hU_card_pos : (0 : ℝ) < (U.card : ℝ) := by
    have : 0 < (δ / 4) * (A.card : ℝ) := by positivity
    linarith
  have hU_card_pos_nat : 0 < U.card := by exact_mod_cast hU_card_pos
  have hU_ne : U.Nonempty := Finset.card_pos.mp hU_card_pos_nat
  -- τ_drc = (ε * c₀²/2) * |B|.  Goal `τ := τ_drc`.
  set τ : ℝ := (ε * c₀ ^ 2 / 2) * (B.card : ℝ) with hτ_def
  have hτ_nn : 0 ≤ τ := by
    rw [hτ_def]
    have h1 : 0 ≤ ε * c₀ ^ 2 / 2 := by positivity
    have h2 : (0 : ℝ) ≤ (B.card : ℝ) := le_of_lt hB_real_pos
    exact mul_nonneg h1 h2
  -- The arithmetic identity: (δ⁵/2¹²)|A|² ≤ (δ/8) · |U| · τ.
  -- We use: (δ/8)|U| ≥ (δ/8)(δ/4)|A| = δ²/32 · |A|, and τ ≥ ?
  -- Key: τ = (δ/16)·c₀²/2·|B| = (δ/32)·c₀²·|A|.
  -- And c₀² · |A₁|² = (δ/2)² · |A|², so c₀² = δ²|A|²/(4·m²).
  -- Hence τ · m² = (δ/32) · (δ²/4) · |A|³ = δ³|A|³/128.
  -- Want: (δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|².
  -- Using |U| ≥ (δ/4)|A| and τ ≥ (δ³/2⁷)|A| (since m ≤ |A|, so |A|³/m² ≥ |A|).
  have hτ_lb : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) ≤ τ := by
    -- τ = (δ/16) · c₀² / 2 · |B| = (δ/32) · c₀² · |A|.
    -- c₀ · m = (δ/2)|A|, so c₀² · m² = δ²|A|²/4.
    -- τ · m² = (δ/32) · δ²|A|²/4 · |A| = δ³|A|³/128.
    -- τ = δ³|A|³ / (128 m²).  Since m ≤ |A|: τ ≥ δ³|A|/128.
    have hc₀sq : c₀ ^ 2 * m ^ 2 = ((δ / 2) * (A.card : ℝ)) ^ 2 := by
      have h := hc₀_mul_m
      calc c₀ ^ 2 * m ^ 2 = (c₀ * m) ^ 2 := by ring
        _ = ((δ / 2) * (A.card : ℝ)) ^ 2 := by rw [h]
    have hm_sq_pos : 0 < m ^ 2 := by positivity
    have hm_sq_le : m ^ 2 ≤ (A.card : ℝ) ^ 2 := by
      have hm_nn : 0 ≤ m := le_of_lt hm_pos
      exact pow_le_pow_left₀ hm_nn hm_le_A 2
    -- τ * m² = (ε * c₀²/2) * |B| * m² = (ε / 2) * (c₀² · m²) * |B|
    --        = (δ / 32) * ((δ/2)|A|)² * |A| = δ³|A|³/128.
    have hτ_m_sq : τ * m ^ 2 = δ ^ 3 / 128 * (A.card : ℝ) ^ 3 := by
      have : τ = (ε * c₀ ^ 2 / 2) * (B.card : ℝ) := hτ_def
      rw [this, hB_real_eq, hε_def]
      have : (δ / 16 * c₀ ^ 2 / 2) * (A.card : ℝ) * m ^ 2
          = (δ / 32) * (c₀ ^ 2 * m ^ 2) * (A.card : ℝ) := by ring
      rw [this, hc₀sq]
      ring
    -- (δ³/2⁷)|A| · m² ≤ τ · m² ↔ (δ³/2⁷)|A| ≤ τ if m² > 0.
    -- Use (δ³/2⁷)|A| · m² ≤ (δ³/2⁷)|A| · |A|² = (δ³/128)|A|³ = τ · m².
    have hineq : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * m ^ 2 ≤ τ * m ^ 2 := by
      rw [hτ_m_sq]
      have : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * m ^ 2 ≤
            (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * (A.card : ℝ) ^ 2 := by
        have hLcoeff_nn : 0 ≤ (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hm_sq_le hLcoeff_nn
      have heq2 : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * (A.card : ℝ) ^ 2 =
          δ ^ 3 / 128 * (A.card : ℝ) ^ 3 := by ring
      linarith
    exact le_of_mul_le_mul_right hineq hm_sq_pos
  -- Now establish the bound (δ⁵/2¹²)|A|² ≤ (δ/8)|U| · τ via
  -- (δ/8)|U| ≥ (δ/8)(δ/4)|A| = δ²/32 · |A| and τ ≥ δ³/128 · |A|, product ≥ δ⁵|A|²/2¹².
  have hUτ_bound : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ := by
    have h1 : (δ / 8) * ((δ / 4) * (A.card : ℝ)) ≤ (δ / 8) * (U.card : ℝ) := by
      have h8 : (0 : ℝ) ≤ δ / 8 := by linarith
      exact mul_le_mul_of_nonneg_left hU_card_lb h8
    have h2 : (δ / 8) * ((δ / 4) * (A.card : ℝ)) * ((δ ^ 3 / 2 ^ 7) * (A.card : ℝ)) ≤
        (δ / 8) * (U.card : ℝ) * τ := by
      have hLHS_nn : 0 ≤ (δ / 8) * ((δ / 4) * (A.card : ℝ)) := by positivity
      have hLHS_nn' : 0 ≤ (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) := by positivity
      exact mul_le_mul h1 hτ_lb hLHS_nn' (le_trans hLHS_nn h1)
    have hrew : (δ / 8) * ((δ / 4) * (A.card : ℝ)) * ((δ ^ 3 / 2 ^ 7) * (A.card : ℝ)) =
        (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 := by ring
    linarith
  -- Bad-pair count in U using the E-codegree.  It is bounded by the E₁-bad count from
  -- graph_pair_dependentRandomChoice, since codeg_E ≥ codeg_{E₁}.
  have hbadCountE : (((U ×ˢ U).filter fun p : G × G ↦
      ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ).card : ℝ)
    ≤ ε * (U.card : ℝ) ^ 2 := by
    -- Pointwise: codeg_E(p) < τ ⟹ codeg_{E₁}(p) ≤ codeg_E(p) < τ.
    have hbadE_sub : ((U ×ˢ U).filter fun p : G × G ↦
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ) ⊆
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨hp.1, ?_⟩
      have hsub : (B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
                  (B.filter (fun y ↦ (p.2, y) ∈ E₁)) ⊆
                  B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E) := by
        intro y hy
        simp only [Finset.mem_inter, Finset.mem_filter] at hy
        simp only [Finset.mem_filter]
        exact ⟨hy.1.1, hE₁_sub_E hy.1.2, hE₁_sub_E hy.2.2⟩
      have hcard : (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
          (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) ≤
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      linarith [hp.2]
    have h := Finset.card_le_card hbadE_sub
    have hreal : (((U ×ˢ U).filter fun p : G × G ↦
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ).card : ℝ) ≤
        (((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ).card : ℝ) := by
      exact_mod_cast h
    -- `τ = (ε * c₀ ^ 2 / 2) * (B.card : ℝ)` by definition; substitute.
    have hfilter_eq :
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ) =
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) <
          (ε * c₀ ^ 2 / 2) * (B.card : ℝ)) := by rfl
    rw [hfilter_eq] at hreal
    linarith
  -- Apply Markov refinement helper.
  obtain ⟨A', hA'_sub_U, hA'_half, hA'_prop⟩ :=
    graph_dependentRandomChoice_markov_refinement (G := G) B U E τ ε hε_pos hU_card_pos hbadCountE
  -- `hA'_half`: (1 - 1/2) * |U| ≤ |A'|, i.e. |U|/2 ≤ |A'|.
  -- `hA'_prop`: ∀ a ∈ A', ((badPartner a).card : ℝ) ≤ 2ε|U| = (δ/8)|U|.
  -- So we get the (δ/8)|U| bound directly: 2 * (δ/16) = δ/8.
  have htwo_eps : (2 : ℝ) * ε = δ / 8 := by rw [hε_def]; ring
  have hA'_prop_clean : ∀ a ∈ A',
      ((U.filter fun a₁ ↦
        ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
        ≤ (δ / 8) * (U.card : ℝ) := by
    intro a ha
    have h := hA'_prop a ha
    have hrew : (2 * ε * (U.card : ℝ)) = (δ / 8) * (U.card : ℝ) := by
      rw [show (2 * ε * (U.card : ℝ)) = 2 * ε * (U.card : ℝ) from rfl, htwo_eps]
    linarith [hrew]
  -- |A'| ≥ |U|/2 ≥ (δ/8)|A|.
  have hA'_card_lb : (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) := by
    have h1 : (δ / 8) * (A.card : ℝ) ≤ (U.card : ℝ) / 2 := by linarith [hU_card_lb]
    have : (1 - 1 / 2) * (U.card : ℝ) = (U.card : ℝ) / 2 := by ring
    linarith [hA'_half, this]
  -- Step 4: popular columns via `graph_dependentRandomChoice_popular_columns`.
  -- Row-degree lower bound for a ∈ U (which is ⊆ A₁): rowDeg_E(a) ≥ (δ/2)|B|.
  have hrowDeg_lb : ∀ a ∈ U, (δ / 2) * (B.card : ℝ) ≤
      ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ) := by
    intro a haU
    have haA₁ : a ∈ A₁ := hU_sub_A₁ haU
    rw [hA₁_def, Finset.mem_filter] at haA₁
    exact haA₁.2
  -- δ/2 > 0 and ≤ 1 since δ ≤ 1.
  have hρ_pos : (0 : ℝ) < δ / 2 := by positivity
  have hρ_le : δ / 2 ≤ 1 := by linarith
  obtain ⟨B', hB'_sub, hB'_lb_drc, hpopCol⟩ :=
    graph_dependentRandomChoice_popular_columns (G := G) A B hAB E hE_sub U hU_sub hU_card_pos
      (δ / 2) hρ_pos hρ_le hrowDeg_lb
  -- (δ/2)/2 = δ/4. So |B'| ≥ (δ/4)|B| = (δ/4)|A| ≥ (δ/8)|A|.
  have hB'_card_lb : (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) := by
    have h3 : (δ / 8) * (A.card : ℝ) ≤ (δ / 4) * (A.card : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hA_nn
    have hquarter_eq : (δ / 2) / 2 * (B.card : ℝ) = (δ / 4) * (A.card : ℝ) := by
      rw [hB_real_eq]; ring
    linarith [hB'_lb_drc, hquarter_eq]
  -- Popular-column property: for b ∈ B', (δ/4)|U| ≤ |{a ∈ U : (a, b) ∈ E}|.
  have hpopCol_clean : ∀ b ∈ B', (δ / 4) * (U.card : ℝ) ≤
      ((U.filter fun a ↦ (a, b) ∈ E).card : ℝ) := by
    intro b hb
    have h := hpopCol b hb
    have hrew : (δ / 2) / 2 * (U.card : ℝ) = (δ / 4) * (U.card : ℝ) := by ring
    linarith [hrew]
  refine ⟨U, A', B', τ, hU_sub, hA'_sub_U, hB'_sub, hτ_nn, hU_card_lb,
    hA'_card_lb, hB'_card_lb, hUτ_bound, hA'_prop_clean, hpopCol_clean⟩

/--
**Pointwise count helper (step 5).** Given the witness from
`graph_dependentRandomChoice_payoff_pointwise_witness`, partition the path-3 Finset
`(B ×ˢ A).filter ((a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E)` by the
second coordinate `q.2 = a₁ ∈ U`. For `a₁` that is a popular neighbour of
`b` and a non-bad partner of `a`, the corresponding fiber has cardinality
`≥ τ`. There are at least `(δ/8)|U|` such `a₁`, giving the final bound
`(δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|²`.
-/
private lemma graph_dependentRandomChoice_payoff_pointwise_count {G : Type*} [DecidableEq G]
    (δ : ℝ) (A B : Finset G) (E : Finset (G × G)) (U A' B' : Finset G) (τ : ℝ)
    (hU_sub : U ⊆ A) (_hA'_sub_U : A' ⊆ U) (_hB'_sub : B' ⊆ B)
    (hτ_nn : 0 ≤ τ)
    (hUτ_bound : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ)
    (hbadPartner : ∀ a ∈ A',
      ((U.filter fun a₁ ↦
        ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
        ≤ (δ / 8) * (U.card : ℝ))
    (hpopCol : ∀ b ∈ B',
      (δ / 4) * (U.card : ℝ) ≤
        ((U.filter fun a₁ ↦ (a₁, b) ∈ E).card : ℝ))
    (a : G) (ha : a ∈ A') (b : G) (hb : b ∈ B') :
    (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
      (((B ×ˢ A).filter fun q : G × G ↦
        (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  -- "Popular neighbours of b in U" and "non-bad partners of a in U".
  set Nb : Finset G := U.filter (fun a₁ ↦ (a₁, b) ∈ E) with hNb_def
  set Bad : Finset G := U.filter (fun a₁ ↦
    ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) < τ) with hBad_def
  have hNb_lb : (δ / 4) * (U.card : ℝ) ≤ (Nb.card : ℝ) := hpopCol b hb
  have hBad_ub : (Bad.card : ℝ) ≤ (δ / 8) * (U.card : ℝ) := hbadPartner a ha
  -- Good := Nb \ Bad.  |Good| ≥ |Nb| - |Bad| ≥ (δ/8)|U|.
  set Good : Finset G := Nb \ Bad with hGood_def
  have hGood_sub_Nb : Good ⊆ Nb := Finset.sdiff_subset
  have hNb_sub_U : Nb ⊆ U := Finset.filter_subset _ _
  have hGood_sub_U : Good ⊆ U := hGood_sub_Nb.trans hNb_sub_U
  have hGood_card_lb : (δ / 8) * (U.card : ℝ) ≤ (Good.card : ℝ) := by
    -- |Nb \ Bad| ≥ |Nb| - |Bad|, via Nb ⊆ (Nb \ Bad) ∪ Bad.
    have hUnion : Nb ⊆ (Nb \ Bad) ∪ Bad := by
      intro x hx
      by_cases hxBad : x ∈ Bad
      · exact Finset.mem_union_right _ hxBad
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxBad⟩)
    have h1 : Nb.card ≤ ((Nb \ Bad) ∪ Bad).card := Finset.card_le_card hUnion
    have h2 : ((Nb \ Bad) ∪ Bad).card ≤ (Nb \ Bad).card + Bad.card :=
      Finset.card_union_le _ _
    have hreal : (Nb.card : ℝ) ≤ ((Nb \ Bad).card : ℝ) + (Bad.card : ℝ) := by
      have : (Nb.card : ℕ) ≤ (Nb \ Bad).card + Bad.card := le_trans h1 h2
      exact_mod_cast this
    have hGood_card_eq : ((Nb \ Bad).card : ℝ) = (Good.card : ℝ) := by
      rw [hGood_def]
    linarith [hreal, hNb_lb, hBad_ub, hGood_card_eq]
  -- For each a₁ ∈ Good: (a₁, b) ∈ E and codeg_E(a, a₁) ≥ τ.
  have hGood_codeg : ∀ a₁ ∈ Good,
      τ ≤ ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) ∧ (a₁, b) ∈ E := by
    intro a₁ ha₁
    rw [hGood_def, Finset.mem_sdiff, hNb_def, Finset.mem_filter, hBad_def,
      Finset.mem_filter] at ha₁
    obtain ⟨⟨ha₁U, ha₁bE⟩, hnotBad⟩ := ha₁
    refine ⟨?_, ha₁bE⟩
    by_contra hlt
    push Not at hlt
    exact hnotBad ⟨ha₁U, hlt⟩
  -- Path Finset of interest.
  set paths : Finset (G × G) := (B ×ˢ A).filter fun q : G × G ↦
    (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E with hpaths_def
  -- Fiber over the second coordinate: for each a₁, witness pairs (b₁, a₁).
  set fiber : G → Finset (G × G) := fun a₁ ↦
    (B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).image (fun b₁ ↦ (b₁, a₁))
    with hfiber_def
  -- fiber a₁ has the same cardinality as the inner filter (image of an injection).
  have hfiber_card : ∀ a₁,
      (fiber a₁).card = (B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card := by
    intro a₁
    rw [hfiber_def]
    apply Finset.card_image_of_injective
    intro x y hxy
    exact (Prod.mk.injEq _ _ _ _).mp hxy |>.1
  -- For a₁ ∈ Good, fiber a₁ ⊆ paths.
  have hfiber_sub : ∀ a₁ ∈ Good, fiber a₁ ⊆ paths := by
    intro a₁ ha₁ p hp
    rw [hfiber_def, Finset.mem_image] at hp
    obtain ⟨b₁, hb₁, hpeq⟩ := hp
    rw [Finset.mem_filter] at hb₁
    obtain ⟨hb₁B, habE, ha₁b₁E⟩ := hb₁
    have ha₁U : a₁ ∈ U := hGood_sub_U ha₁
    have ha₁A : a₁ ∈ A := hU_sub ha₁U
    obtain ⟨_, ha₁bE⟩ := hGood_codeg a₁ ha₁
    rw [hpaths_def, Finset.mem_filter, Finset.mem_product]
    rw [← hpeq]
    exact ⟨⟨hb₁B, ha₁A⟩, habE, ha₁b₁E, ha₁bE⟩
  -- Pairwise disjointness of fibers (different a₁ → different second coord).
  have hfiber_disjoint : (Good : Set G).PairwiseDisjoint fiber := by
    intro x _ y _ hxy
    refine Finset.disjoint_left.mpr ?_
    intro p hpx hpy
    rw [hfiber_def, Finset.mem_image] at hpx hpy
    obtain ⟨bx, _, hpx_eq⟩ := hpx
    obtain ⟨by_, _, hpy_eq⟩ := hpy
    have hsnd : p.2 = x := by rw [← hpx_eq]
    have hsnd' : p.2 = y := by rw [← hpy_eq]
    exact hxy (hsnd.symm.trans hsnd')
  -- |⋃_{a₁ ∈ Good} fiber a₁| = Σ_{a₁ ∈ Good} |fiber a₁|.
  have hbiUnion_card : (Good.biUnion fiber).card = ∑ a₁ ∈ Good, (fiber a₁).card := by
    exact Finset.card_biUnion (fun x hx y hy hxy ↦ hfiber_disjoint hx hy hxy)
  -- The biUnion is contained in paths.
  have hbiUnion_sub : Good.biUnion fiber ⊆ paths := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨a₁, ha₁, hp⟩ := hp
    exact hfiber_sub a₁ ha₁ hp
  have hcard_path_lb : (∑ a₁ ∈ Good, (fiber a₁).card : ℕ) ≤ paths.card := by
    calc (∑ a₁ ∈ Good, (fiber a₁).card : ℕ)
        = (Good.biUnion fiber).card := hbiUnion_card.symm
      _ ≤ paths.card := Finset.card_le_card hbiUnion_sub
  have hcard_path_lb_real : (∑ a₁ ∈ Good, ((fiber a₁).card : ℝ)) ≤ (paths.card : ℝ) := by
    have h : ((∑ a₁ ∈ Good, (fiber a₁).card : ℕ) : ℝ) ≤ (paths.card : ℝ) := by
      exact_mod_cast hcard_path_lb
    push_cast at h; exact h
  -- Σ_{a₁ ∈ Good} |fiber a₁| ≥ |Good| · τ.
  have hsum_lb : (Good.card : ℝ) * τ ≤ ∑ a₁ ∈ Good, ((fiber a₁).card : ℝ) := by
    rw [show (Good.card : ℝ) * τ = ∑ _a₁ ∈ Good, τ from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a₁ ha₁ ↦ ?_
    have hcard := hfiber_card a₁
    have hcodeg := (hGood_codeg a₁ ha₁).1
    have : ((fiber a₁).card : ℝ) =
        ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) := by
      exact_mod_cast hcard
    rw [this]
    exact hcodeg
  -- Combine: paths ≥ |Good| · τ ≥ (δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|².
  have hGood_τ : (δ / 8) * (U.card : ℝ) * τ ≤ (Good.card : ℝ) * τ :=
    mul_le_mul_of_nonneg_right hGood_card_lb hτ_nn
  linarith [hUτ_bound, hGood_τ, hsum_lb, hcard_path_lb_real]

/--
**DRC payoff: pointwise path-3 count.** Given the pair-DRC witness `U ⊆ A`
(from `graph_pair_dependentRandomChoice`), define the "non-bad" set
`A' := { a ∈ U : few a' ∈ U with codegree < (δ³/2⁷) n }` and the "popular"
set `B' := { b ∈ B : (δ/4) |U| ≤ |N_U(b)| }`. For `a ∈ A'`, `b ∈ B'`, the
length-3 path count `P(a, b) ≥ (δ⁵ / 2¹²) n²`.

Proof: of the `(δ/4)|U|` vertices in `U ∩ N(b)`, at most `(δ/8)|U|` are bad
partners of `a`, leaving `≥ (δ/8)|U|` non-bad partners `a₁`. Each non-bad
partner has `|N(a) ∩ N(a₁)| ≥ (δ³/2⁷) n` choices of `b₁`. Total:
`P(a, b) ≥ (δ/8)|U| · (δ³/2⁷) n ≥ (δ/8)(δ/4)n · (δ³/128) n = (δ⁵/2¹²) n²`.
-/
lemma graph_dependentRandomChoice_payoff_pointwise {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  obtain ⟨U, A', B', τ, hU_sub, hA'_sub_U, hB'_sub, hτ_nn, _hU_card, hA'_card,
    hB'_card, hUτ_bound, hbadPartner, hpopCol⟩ :=
    graph_dependentRandomChoice_payoff_pointwise_witness δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense
  refine ⟨A', B', hA'_sub_U.trans hU_sub, hB'_sub, hA'_card, hB'_card, ?_⟩
  intro a ha b hb
  exact graph_dependentRandomChoice_payoff_pointwise_count δ A B E U A' B' τ hU_sub hA'_sub_U hB'_sub
    hτ_nn hUτ_bound hbadPartner hpopCol a ha b hb

end Finset

/-
Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/

namespace Erdos101.DivisionRatios

open EuclideanGeometry
open scoped Classical Pointwise

section VectorSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- No five points of the set lie on an affine line in the ambient vector space. -/
abbrev NoFiveCollinear (S : Set E) : Prop :=
  ∀ T : Set E, T ⊆ S → T.Finite → T.ncard = 5 → ¬ Collinear ℝ T

omit [DecidableEq E] in
private theorem card_le_four {A U : Finset E} (hA : NoFiveCollinear (A : Set E))
    (hU : U ⊆ A) (hline : Collinear ℝ (U : Set E)) : U.card ≤ 4 := by
  by_contra! h
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq (show 5 ≤ U.card by omega)
  apply hA (T : Set E) (Finset.coe_subset.mpr (hT.trans hU)) T.finite_toSet
    (by simpa using hcard)
  exact Collinear.subset (Finset.coe_subset.mpr hT) hline

/-- Translating along any finite scalar set on one line produces at most
four representations of each point in the receiving set. -/
theorem line_packing_into {A C : Finset E} (hA : NoFiveCollinear (A : Set E))
    {p d : E} (hd : d ≠ 0) (I : Finset ℝ)
    (hm : ∀ a ∈ A, ∀ t ∈ I, (p+t • d)+a ∈ C) :
    A.card*I.card ≤ C.card*4 := by
  classical
  let P := A ×ˢ I
  let f : E × ℝ → E := fun z => (p+z.2 • d)+z.1
  have maps : (P : Set (E × ℝ)).MapsTo f C := by
    intro z hz
    obtain ⟨ha,ht⟩ := Finset.mem_product.mp hz
    exact hm _ ha _ ht
  have count (z : E) : (P.filter (fun e => f e = z)).card ≤ 4 := by
    let T := P.filter (fun e => f e = z)
    have inject : (T : Set (E × ℝ)).InjOn Prod.fst := by
      rintro ⟨a,t⟩ ht ⟨b,u⟩ hu hab
      change a = b at hab
      subst b
      have he := (Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hu).2.symm
      change (p+t • d)+a = (p+u • d)+a at he
      exact Prod.ext rfl ((smul_left_injective ℝ hd) (add_left_cancel (add_right_cancel he)))
    change T.card ≤ 4
    rw [← Finset.card_image_of_injOn inject]
    apply card_le_four hA
    · rintro a ha
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
    · rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨z-p,d,?_⟩
      rintro a ha
      obtain ⟨⟨b,t⟩,ht,rfl⟩ := Finset.mem_image.mp ha
      have he := (Finset.mem_filter.mp ht).2
      change (p+t • d)+b = z at he
      refine ⟨-t,?_⟩
      change b = -t • d + (z-p)
      rw [neg_smul,← he]
      abel
  calc
    _ = P.card := by simp [P]
    _ = _ := Finset.card_eq_sum_card_fiberwise maps
    _ ≤ ∑ _z ∈ C, 4 := Finset.sum_le_sum fun z _ => count z
    _ = _ := by simp

end VectorSpace

end Erdos101.DivisionRatios

namespace Erdos101.ProjectiveSums

open EuclideanGeometry
open scoped Classical

abbrev Height := ℝ² → ℝˣ

/-- A homogeneous representative of an affine point. -/
def lift (h : Height) (p : ℝ²) : ℝ × ℝ² := ((h p : ℝ), (h p : ℝ) • p)

theorem lift_injective (h : Height) : Function.Injective (lift h) := by
  apply Function.LeftInverse.injective (g := fun v : ℝ × ℝ² => v.1⁻¹ • v.2)
  intro x
  simp [lift, smul_smul]

private theorem project_mem_line (h : Height) {x y z : ℝ²}
    (hz : lift h z ∈ line[ℝ,lift h x,lift h y]) : z ∈ line[ℝ,x,y] := by
  obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hz
  rw [AffineMap.lineMap_apply_module] at ht
  have hs := congrArg Prod.fst ht
  change (1-t)*(h x : ℝ) + t*(h y : ℝ) = (h z : ℝ) at hs
  have hv := congrArg Prod.snd ht
  change (1-t) • ((h x : ℝ) • x) + t • ((h y : ℝ) • y) = (h z : ℝ) • z at hv
  rw [smul_smul, smul_smul] at hv
  let s := t * (h y : ℝ) / (h z : ℝ)
  have h₂ : (h z : ℝ)*s = t*(h y : ℝ) := by
    dsimp [s]
    field_simp
  have h₁ : (h z : ℝ)*(1-s) = (1-t)*(h x : ℝ) := by
    rw [mul_sub,mul_one,h₂]
    linarith only [hs]
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨s, (smul_right_injective ℝ² (h z).ne_zero) ?_⟩
  simpa only [AffineMap.lineMap_apply_module,smul_add,smul_smul,h₁,h₂] using hv

/-- The affine span of any collinear lifted points projects into a single
projective line, preserving the five-point obstruction in the finite image. -/
theorem lift_no_five {S : Finset ℝ²} (hS : NonCollinearFor 5 (S : Set ℝ²))
    (h : Height) : DivisionRatios.NoFiveCollinear (S.image (lift h) : Set (ℝ × ℝ²)) := by
  classical
  intro T hT hfin hcard hcol
  let Q := S.filter (fun x => lift h x ∈ T)
  have himage : Q.image (lift h) = hfin.toFinset := by
    ext v
    rw [hfin.mem_toFinset]
    constructor
    · rintro hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hx).2
    · intro hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (hT hv)
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hv⟩,rfl⟩
  have hQ : Q.card = 5 := calc
    Q.card = (Q.image (lift h)).card := (Finset.card_image_of_injective _ (lift_injective h)).symm
    _ = hfin.toFinset.card := congrArg Finset.card himage
    _ = 5 := (Set.ncard_eq_toFinset_card T hfin).symm.trans hcard
  obtain ⟨x,y,hx,hy,hxy⟩ := Finset.one_lt_card_iff.mp (show 1 < Q.card by omega)
  apply hS (Q : Set ℝ²) (Finset.coe_subset.mpr (Finset.filter_subset ..)) Q.finite_toSet
    (by simpa only [Set.ncard_coe_finset] using hQ)
  apply (collinear_iff_of_mem hx).mpr
  refine ⟨y-x,?_⟩
  intro z hz
  have hl := hcol.mem_affineSpan_of_mem_of_ne (Finset.mem_filter.mp hx).2
    (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2 ((lift_injective h).ne hxy)
  obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp (project_mem_line h hl)
  exact ⟨t,by simpa only [AffineMap.lineMap_apply_module',vadd_eq_add] using ht.symm⟩

end Erdos101.ProjectiveSums

namespace Erdos101OrderedGrid

open scoped Classical

abbrev Pos := ℕ × ℕ

def grid (n : ℕ) : Finset Pos := Finset.range n ×ˢ Finset.range n
def block (k : ℕ) (p : Pos) : Pos := (p.1/k,p.2/k)
def fiber (G : Finset Pos) (k : ℕ) (c : Pos) := G.filter (fun p => block k p = c)
def occupied (G : Finset Pos) (k : ℕ) := G.image (block k)
def good (G : Finset Pos) (k r : ℕ) := (occupied G k).filter (fun c => r ≤ (fiber G k c).card)

/-- Increasing coordinate pairs when `up` is true, decreasing pairs otherwise. -/
def aligned (up : Bool) (p q : Pos) : Prop :=
  p.1 ≤ q.1 ∧ (if up then p.2 ≤ q.2 else q.2 ≤ p.2)

def chain (up : Bool) (G : Finset Pos) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, aligned up p q ∨ aligned up q p

def twoChains (G : Finset Pos) : Prop :=
  ∃ B C : Finset Pos, ∃ b c : Bool, G = B ∪ C ∧ chain b B ∧ chain c C

lemma fiber_card_le (G : Finset Pos) {k : ℕ} (hk : 0 < k) (c : Pos) :
    (fiber G k c).card ≤ k^2 := by
  let rem : Pos → Pos := fun p => (p.1%k,p.2%k)
  have hinj : Set.InjOn rem (fiber G k c : Finset Pos) := by
    intro p hp q hq he
    have h := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    change p.1/k = q.1/k at hx
    change p.2/k = q.2/k at hy
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    change p.1%k = q.1%k at h₁
    change p.2%k = q.2%k at h₂
    apply Prod.ext
    · rw [← Nat.mod_add_div p.1 k,h₁,hx,Nat.mod_add_div]
    · rw [← Nat.mod_add_div p.2 k,h₂,hy,Nat.mod_add_div]
  have hsub : (fiber G k c).image rem ⊆ grid k := by
    intro p hp
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk),
      Finset.mem_range.mpr (Nat.mod_lt _ hk)⟩
  rw [← Finset.card_image_of_injOn hinj]
  simpa [grid,pow_two] using Finset.card_le_card hsub

lemma occupied_chain {G : Finset Pos} {b : Bool} (h : chain b G) (k : ℕ) :
    chain b (occupied G k) := by
  have mono {p q : Pos} (hp : aligned b p q) : aligned b (block k p) (block k q) := by
    cases b <;> simp [aligned,block] at hp ⊢ <;>
      exact ⟨Nat.div_le_div_right hp.1,Nat.div_le_div_right hp.2⟩
  intro p hp q hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  exact (h x hx y hy).imp mono mono

lemma occupied_subset {G : Finset Pos} {n : ℕ} (h : G ⊆ grid n) (k : ℕ) :
    occupied G k ⊆ grid (n/k+1) := by
  intro p hp
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp (h hx)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_range.mp ha).le)),
     Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_range.mp hb).le))⟩

lemma chain_card {G : Finset Pos} {m : ℕ} (hgrid : G ⊆ grid (m+1)) {b : Bool}
    (hchain : chain b G) : G.card ≤ 2*(m+1) := by
  let code (p : Pos) := p.1 + (if b then p.2 else m-p.2)
  have coords {p : Pos} (hp : p ∈ G) : p.1 ≤ m ∧ p.2 ≤ m :=
    ⟨Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp (hgrid hp)).1),
     Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp (hgrid hp)).2)⟩
  have equal {p q : Pos} (hp : p ∈ G) (hq : q ∈ G) (ha : aligned b p q)
      (he : code p = code q) : p = q := by
    obtain ⟨px,py⟩ := coords hp
    obtain ⟨qx,qy⟩ := coords hq
    cases b <;> simp [aligned,code] at ha he <;> apply Prod.ext <;> omega
  have hinj : Set.InjOn code (G : Set Pos) := by
    intro p hp q hq he
    rcases hchain p hp q hq with h | h
    · exact equal hp hq h he
    · exact (equal hq hp h he.symm).symm
  have hsub : G.image code ⊆ Finset.range (2*(m+1)) := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨px,py⟩ := coords hp
    apply Finset.mem_range.mpr
    cases b <;> simp [code] <;> omega
  rw [← Finset.card_image_of_injOn hinj]
  simpa using Finset.card_le_card hsub

lemma occupied_count {G : Finset Pos} {n : ℕ} (hgrid : G ⊆ grid n) (h : twoChains G) (k : ℕ) :
    (occupied G k).card ≤ 4*(n/k+1) := by
  obtain ⟨B,C,b,c,rfl,hB,hC⟩ := h
  have h₁ := chain_card (occupied_subset (Finset.subset_union_left.trans hgrid) k) (occupied_chain hB k)
  have h₂ := chain_card (occupied_subset (Finset.subset_union_right.trans hgrid) k) (occupied_chain hC k)
  change ((B ∪ C).image (block k)).card ≤ _
  rw [Finset.image_union]
  exact (Finset.card_union_le ..).trans (by change (occupied B k).card + (occupied C k).card ≤ _; omega)

lemma graph_count {G : Finset Pos} {k r : ℕ} (hk : 0 < k) :
    G.card ≤ (occupied G k).card*r + (good G k r).card*k^2 := by
  have hfib (c : Pos) :
      (fiber G k c).card ≤ r + (if r ≤ (fiber G k c).card then k^2 else 0) := by
    split_ifs
    · exact (fiber_card_le G hk c).trans (by omega)
    · omega
  calc
    G.card = ∑ c ∈ occupied G k, (fiber G k c).card := Finset.card_eq_sum_card_image .. 
    _ ≤ ∑ c ∈ occupied G k, (r + (if r ≤ (fiber G k c).card then k^2 else 0)) :=
      Finset.sum_le_sum (fun c _ => hfib c)
    _ = (occupied G k).card*r + (good G k r).card*k^2 := by
      simp [Finset.sum_add_distrib,← Finset.sum_filter,good]

lemma good_per_graph {G : Finset Pos} {n t k r b : ℕ} (hk : 0 < k) (hn : k ≤ n)
    (large : 4*t*r*b ≤ k) (occ : (occupied G k).card ≤ b*(n/k+1)) (hrich : n ≤ t*G.card) :
    n ≤ 2*t*k^2*(good G k r).card := by
  have hd : 1 ≤ n/k := (Nat.le_div_iff_mul_le hk).mpr (by simpa using hn)
  have hm : 2*(t*((occupied G k).card*r)) ≤ n := calc
    _ ≤ 2*(t*((b*(n/k+1))*r)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ occ))
    _ = (2*t*r*b)*(n/k+1) := by ring
    _ ≤ (2*t*r*b)*(n/k+n/k) := Nat.mul_le_mul_left _ (Nat.add_le_add_left hd _)
    _ = (4*t*r*b)*(n/k) := by ring
    _ ≤ k*(n/k) := Nat.mul_le_mul_right _ large
    _ = (n/k)*k := Nat.mul_comm ..
    _ ≤ n := Nat.div_mul_le_self n k
  have bound := Nat.mul_le_mul_left t (graph_count (G := G) (r := r) hk)
  nlinarith only [hrich,bound,hm]

lemma good_per_cell {ι : Type*} (A : Finset ι) (graphs : ι → Finset Pos) {n k r M : ℕ}
    (hk : 0 < k) (hg : ∀ i ∈ A, graphs i ⊆ grid n)
    (hm : ∀ T : Finset Pos, T.card = r → (A.filter (fun i => T ⊆ graphs i)).card ≤ M) (c : Pos) :
    (A.filter (fun i => c ∈ good (graphs i) k r)).card ≤ k^(2*r)*M := by
  classical
  let P := fiber (grid n) k c
  let samples := P.powersetCard r
  have hsub : A.filter (fun i => c ∈ good (graphs i) k r) ⊆
      samples.biUnion (fun T => A.filter (fun i => T ⊆ graphs i)) := by
    intro i hi
    obtain ⟨hiA,hgood⟩ := Finset.mem_filter.mp hi
    obtain ⟨T,hT,hsize⟩ := Finset.exists_subset_card_eq (Finset.mem_filter.mp hgood).2
    have hTP : T ⊆ P := hT.trans (Finset.filter_subset_filter _ (hg i hiA))
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_powersetCard.mpr ⟨hTP,hsize⟩,
      Finset.mem_filter.mpr ⟨hiA,hT.trans (Finset.filter_subset ..)⟩⟩
  have hnum : samples.card ≤ k^(2*r) := calc
    samples.card = P.card.choose r := Finset.card_powersetCard ..
    _ ≤ P.card^r := Nat.choose_le_pow ..
    _ ≤ (k^2)^r := Nat.pow_le_pow_left (fiber_card_le _ hk _) r
    _ = _ := (pow_mul ..).symm
  calc
    _ ≤ _ := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _T ∈ samples, M := Finset.sum_le_sum (fun T hT => hm T (Finset.mem_powersetCard.mp hT).2)
    _ = samples.card*M := by simp
    _ ≤ _ := Nat.mul_le_mul_right M hnum

/-- A rich family of bounded block occupancy has linear size when prescribed
r-point sets lie on at most M family members. -/
theorem rich_components (A : Finset ι) (graphs : ι → Finset Pos) {n t k r b M : ℕ}
    (hk : 0 < k) (hn : k ≤ n) (large : 4*t*r*b ≤ k) (hg : ∀ i ∈ A, graphs i ⊆ grid n)
    (hc : ∀ i ∈ A, (occupied (graphs i) k).card ≤ b*(n/k+1)) (hr : ∀ i ∈ A, n ≤ t*(graphs i).card)
    (hm : ∀ T : Finset Pos, T.card = r → (A.filter (fun i => T ⊆ graphs i)).card ≤ M) :
    A.card ≤ 8*t*k^(2+2*r)*M*n := by
  classical
  let cells := grid (n/k+1)
  have hn' : 0 < n := by omega
  have cellsub {i : ι} (hi : i ∈ A) : good (graphs i) k r ⊆ cells :=
    (Finset.filter_subset ..).trans (occupied_subset (hg i hi) k)
  have decomp {i : ι} (hi : i ∈ A) :
      cells.filter (fun c => c ∈ good (graphs i) k r) = good (graphs i) k r := by
    ext c
    exact Finset.mem_filter.trans (and_iff_right_of_imp (fun h => cellsub hi h))
  have hsum : ∑ i ∈ A, (good (graphs i) k r).card ≤ cells.card*(k^(2*r)*M) := calc
    _ = ∑ i ∈ A, (cells.filter (fun c => c ∈ good (graphs i) k r)).card :=
      Finset.sum_congr rfl (fun i hi => by rw [decomp hi])
    _ = ∑ c ∈ cells, (A.filter (fun i => c ∈ good (graphs i) k r)).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ..
    _ ≤ ∑ _c ∈ cells, k^(2*r)*M := Finset.sum_le_sum (fun c _ => good_per_cell A graphs hk hg hm c)
    _ = _ := by simp
  have bound : cells.card ≤ 4*n^2 := by
    have hd := Nat.div_le_self n k
    calc
      cells.card = (n/k+1)^2 := by simp [cells,grid,pow_two]
      _ ≤ (2*n)^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  have htotal : A.card*n ≤ (8*t*k^(2+2*r)*M*n)*n := calc
    _ = ∑ _i ∈ A, n := by simp
    _ ≤ ∑ i ∈ A, (2*t*k^2)*(good (graphs i) k r).card :=
      Finset.sum_le_sum (fun i hi => good_per_graph hk hn large (hc i hi) (hr i hi))
    _ = (2*t*k^2)*∑ i ∈ A, (good (graphs i) k r).card := (Finset.mul_sum ..).symm
    _ ≤ (2*t*k^2)*(cells.card*(k^(2*r)*M)) := Nat.mul_le_mul_left _ hsum
    _ ≤ (2*t*k^2)*((4*n^2)*(k^(2*r)*M)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ bound)
    _ = _ := by rw [pow_add]; ring
  exact Nat.le_of_mul_le_mul_right htotal hn'

/-- For a two-piece graph, triple multiplicity suffices. -/
theorem rich_graphs (A : Finset ι) (graphs : ι → Finset Pos) {n t M : ℕ}
    (ht : 0 < t) (hn : 64*t ≤ n) (hg : ∀ i ∈ A, graphs i ⊆ grid n)
    (hc : ∀ i ∈ A, twoChains (graphs i)) (hr : ∀ i ∈ A, n ≤ t*(graphs i).card)
    (hm : ∀ T : Finset Pos, T.card = 3 → (A.filter (fun i => T ⊆ graphs i)).card ≤ M) :
    A.card ≤ 8*t*(64*t)^8*M*n :=
  rich_components A graphs (by omega) hn (b := 4) (r := 3) (by omega) hg
    (fun i hi => occupied_count (hg i hi) (hc i hi) _) hr hm

end Erdos101OrderedGrid

namespace Erdos101SecantSamples

open EuclideanGeometry Erdos101OrderedGrid
open scoped Classical

/-- Count a shared pivot twice by its two centers. The estimate requires only
the total number of assigned pivots across the centers. -/
theorem common_pivots (centers : Finset ι) (U : Finset α) (D : ι → Finset α)
    [DecidableEq α] (hD : ∀ p ∈ centers, D p ⊆ U) :
    (∑ p ∈ centers, (D p).card)^2 ≤ U.card *
      ∑ e ∈ centers ×ˢ centers, (D e.1 ∩ D e.2).card := by
  classical
  let T (y : α) := centers.filter (fun p => y ∈ D p)
  have hsingle (p : ι) (hp : p ∈ centers) : U.filter (fun y => y ∈ D p) = D p := by
    ext y
    exact Finset.mem_filter.trans (and_iff_right_of_imp (fun hy => hD p hp hy))
  have hmass : ∑ p ∈ centers, (D p).card = ∑ y ∈ U, (T y).card := calc
    _ = ∑ p ∈ centers, (U.filter (fun y => y ∈ D p)).card :=
      Finset.sum_congr rfl (fun p hp => by rw [hsingle p hp])
    _ = _ := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ..
  have hpairs (y : α) : (centers ×ˢ centers).filter
      (fun e => y ∈ D e.1 ∩ D e.2) = T y ×ˢ T y := by
    ext ⟨p,q⟩
    simp [T,and_assoc,and_left_comm]
  have hinter (e : ι × ι) (he : e ∈ centers ×ˢ centers) :
      U.filter (fun y => y ∈ D e.1 ∩ D e.2) = D e.1 ∩ D e.2 := by
    ext y
    exact Finset.mem_filter.trans (and_iff_right_of_imp (fun h =>
      hD _ (Finset.mem_product.mp he).1 (Finset.mem_inter.mp h).1))
  have second : ∑ e ∈ centers ×ˢ centers, (D e.1 ∩ D e.2).card = ∑ y ∈ U, (T y).card^2 := calc
    _ = ∑ e ∈ centers ×ˢ centers, (U.filter (fun y => y ∈ D e.1 ∩ D e.2)).card :=
      Finset.sum_congr rfl (fun e he => by rw [hinter e he])
    _ = ∑ y ∈ U, ((centers ×ˢ centers).filter (fun e => y ∈ D e.1 ∩ D e.2)).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ..
    _ = _ := Finset.sum_congr rfl (fun y _ => by rw [hpairs,Finset.card_product,pow_two])
  rw [hmass,second]
  exact sq_sum_le_card_mul_sum_sq

end Erdos101SecantSamples

namespace Erdos101ConicSecants

open EuclideanGeometry MvPolynomial
open scoped Classical

structure Mob where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

namespace Mob
def det (g : Mob) : ℝ := g.a*g.d-g.b*g.c
def hit (g : Mob) (x y : ℝ) : Prop := (g.c*x+g.d)*y = g.a*x+g.b
theorem denom_ne {g : Mob} {x y : ℝ} (hd : g.det ≠ 0) (h : g.hit x y) :
    g.c*x+g.d ≠ 0 := by
  intro he
  apply hd
  unfold hit at h
  unfold det
  linear_combination (g.a-g.c*y)*he + g.c*h

theorem hit_unique {g : Mob} {x y z : ℝ} (hd : g.det ≠ 0)
    (hy : g.hit x y) (hz : g.hit x z) : y = z := by
  exact mul_left_cancel₀ (denom_ne hd hy) (hy.trans hz.symm)

theorem difference {g : Mob} {x y u v : ℝ} (h : g.hit x u) (j : g.hit y v) :
    (v-u)*(g.c*y+g.d)*(g.c*x+g.d) = g.det*(y-x) := by
  unfold hit det at *
  linear_combination (g.c*x+g.d)*j - (g.c*y+g.d)*h
end Mob

end Erdos101ConicSecants

namespace Erdos101Parabola

open EuclideanGeometry Erdos101ConicSecants Erdos101OrderedGrid
open scoped Classical

def rank (X : Finset ℝ) (x : ℝ) := (X.filter (· < x)).card
def ranks (X : Finset ℝ) (p : ℝ × ℝ) : Pos := (rank X p.1,rank X p.2)
def graph (X : Finset ℝ) (g : Mob) := (X ×ˢ X).filter (fun p => g.hit p.1 p.2)
def ranked (X : Finset ℝ) (g : Mob) := (graph X g).image (ranks X)

lemma rank_mono (X : Finset ℝ) : Monotone (rank X) := by
  intro x y h
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.trans_le h⟩

lemma rank_strict (X : Finset ℝ) {x y : ℝ} (hx : x ∈ X) (h : x < y) : rank X x < rank X y := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
  · intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.trans h⟩
  · intro he
    have hm : x ∈ X.filter (· < y) := Finset.mem_filter.mpr ⟨hx,h⟩
    rw [← he] at hm
    exact (lt_irrefl x) (Finset.mem_filter.mp hm).2

lemma rank_lt_card (X : Finset ℝ) {x : ℝ} (hx : x ∈ X) : rank X x < X.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset ..,?_⟩
  intro he
  have hm : x ∈ X.filter (· < x) := by rw [he]; exact hx
  exact (lt_irrefl x) (Finset.mem_filter.mp hm).2

lemma ranks_inj (X : Finset ℝ) : Set.InjOn (ranks X) (↑(X ×ˢ X) : Set (ℝ × ℝ)) := by
  have inj {x y : ℝ} (hx : x ∈ X) (hy : y ∈ X) (he : rank X x = rank X y) : x = y := by
    rcases lt_trichotomy x y with h|h|h
    · exact False.elim ((rank_strict X hx h).ne he)
    · exact h
    · exact False.elim ((rank_strict X hy h).ne he.symm)
  intro p hp q hq h
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
  obtain ⟨hz,hw⟩ := Finset.mem_product.mp hq
  exact Prod.ext (inj hx hz (congrArg Prod.fst h)) (inj hy hw (congrArg Prod.snd h))

lemma ranked_card (X : Finset ℝ) (g : Mob) : (ranked X g).card = (graph X g).card :=
  Finset.card_image_of_injOn ((ranks_inj X).mono (Finset.coe_subset.mpr (Finset.filter_subset ..)))

lemma ranked_subset (X : Finset ℝ) (g : Mob) {n : ℕ} (h : X.card ≤ n) : ranked X g ⊆ grid n := by
  intro u hu
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr ((rank_lt_card X hx).trans_le h),
    Finset.mem_range.mpr ((rank_lt_card X hy).trans_le h)⟩

lemma hit_of_ranked {X : Finset ℝ} {p : ℝ × ℝ} {g : Mob} (hp : p ∈ X ×ˢ X)
    (h : ranks X p ∈ ranked X g) : g.hit p.1 p.2 := by
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp h
  obtain ⟨hqX,hqg⟩ := Finset.mem_filter.mp hq
  exact (ranks_inj X hqX hp he) ▸ hqg

private lemma ordered_branch (X : Finset ℝ) (g : Mob) (B : Finset (ℝ × ℝ))
    (hg : B ⊆ graph X g)
    (hs : ∀ p ∈ B, ∀ q ∈ B, 0 < (g.c*q.1+g.d)*(g.c*p.1+g.d)) :
    chain (decide (0 ≤ g.det)) (B.image (ranks X)) := by
  have forward {p q : ℝ × ℝ} (hp : p ∈ B) (hq : q ∈ B) (h : p.1 ≤ q.1) :
      aligned (decide (0 ≤ g.det)) (ranks X p) (ranks X q) := by
    have he := Mob.difference (Finset.mem_filter.mp (hg hp)).2 (Finset.mem_filter.mp (hg hq)).2
    rw [mul_assoc] at he
    have hh := hs p hp q hq
    refine ⟨rank_mono X h,?_⟩
    by_cases hd : 0 ≤ g.det
    · simp only [hd,decide_true,ite_true,ranks]
      apply rank_mono
      apply sub_nonneg.mp
      exact nonneg_of_mul_nonneg_left (he.trans_ge (mul_nonneg hd (sub_nonneg.mpr h))) hh
    · simp only [hd,decide_false,ranks]
      apply rank_mono
      apply sub_nonpos.mp
      exact nonpos_of_mul_nonpos_left (he.trans_le (mul_nonpos_of_nonpos_of_nonneg
        (le_of_not_ge hd) (sub_nonneg.mpr h))) hh
  intro u hu v hv
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  exact (le_total p.1 q.1).imp (forward hp hq) (forward hq hp)

theorem graph_two_chains (X : Finset ℝ) (g : Mob) (hd : g.det ≠ 0) : twoChains (ranked X g) := by
  let B := (graph X g).filter (fun p => 0 < g.c*p.1+g.d)
  let C := (graph X g).filter (fun p => ¬0 < g.c*p.1+g.d)
  have hu : B ∪ C = graph X g := Finset.filter_union_filter_not_eq ..
  refine ⟨B.image (ranks X),C.image (ranks X),decide (0 ≤ g.det),decide (0 ≤ g.det),?_,?_,?_⟩
  · exact (congrArg (Finset.image (ranks X)) hu.symm).trans (Finset.image_union ..)
  · apply ordered_branch X g B (Finset.filter_subset ..)
    intro p hp q hq
    exact mul_pos (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hp).2
  · apply ordered_branch X g C (Finset.filter_subset ..)
    have neg {p : ℝ × ℝ} (hp : p ∈ C) : g.c*p.1+g.d < 0 := by
      obtain ⟨hpG,hn⟩ := Finset.mem_filter.mp hp
      exact lt_of_le_of_ne (le_of_not_gt hn) (Mob.denom_ne hd (Finset.mem_filter.mp hpG).2)
    intro p hp q hq
    exact mul_pos_of_neg_of_neg (neg hq) (neg hp)

end Erdos101Parabola

namespace Erdos101CentralMaps

open EuclideanGeometry
open scoped Classical

def shift (t : ℝ² → ℝ) (p : ℝ²) : ℝ² := (1-t p) • p

/-- This vector vanishes exactly when the intercept differences are in the
same ratio as the slope differences, provided two slopes are different. -/
def defect (t : ℝ² → ℝ) (p q r : ℝ²) : ℝ² :=
  (t q-t p) • (shift t r-shift t p) - (t r-t p) • (shift t q-shift t p)

def graphKey (f : ℝ² →ₗ[ℝ] ℝ) (t : ℝ² → ℝ) (p : ℝ²) : ℝ × ℝ :=
  (t p,f (shift t p))

theorem generic_form (S : Finset ℝ²) (t : ℝ² → ℝ) :
    ∃ f : ℝ² →ₗ[ℝ] ℝ, (S : Set ℝ²).InjOn f ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, f (defect t p q r) = 0 → defect t p q r = 0 := by
  classical
  let D := (S ×ˢ S).image (fun e => e.1-e.2) ∪
    (S ×ˢ (S ×ˢ S)).image (fun e => defect t e.1 e.2.1 e.2.2)
  let W := D.erase 0
  obtain ⟨f,hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    (fun w : W => w.val) (fun w => (Finset.mem_erase.mp w.property).1)
  have detect (v : ℝ²) (hv : v ∈ D) (hz : f v = 0) : v = 0 := by
    by_contra hn
    exact hf ⟨v,Finset.mem_erase.mpr ⟨hn,hv⟩⟩ hz
  refine ⟨f,?_,?_⟩
  · intro p hp q hq he
    exact sub_eq_zero.mp (detect (p-q) (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,rfl⟩)) (by simp [he]))
  · intro p hp q hq r hr
    exact detect _ (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨(p,q,r),Finset.mem_product.mpr ⟨hp,Finset.mem_product.mpr ⟨hq,hr⟩⟩,rfl⟩))

end Erdos101CentralMaps

namespace Erdos101HomothetyOrbits

open EuclideanGeometry Erdos101.DivisionRatios
open scoped Classical Pointwise

structure Hom where
  scale : ℝˣ
  shift : ℝ²

theorem Hom.ext {g h : Hom} (hs : g.scale = h.scale) (hv : g.shift = h.shift) : g = h := by
  cases g; cases h; cases hs; cases hv; rfl

instance : One Hom := ⟨⟨1,0⟩⟩
instance : Mul Hom := ⟨fun g h => ⟨g.scale*h.scale,g.shift+g.scale • h.shift⟩⟩
instance : Inv Hom := ⟨fun g => ⟨g.scale⁻¹,-(g.scale⁻¹ • g.shift)⟩⟩

instance : Group Hom where
  mul_assoc g h k := Hom.ext (mul_assoc ..) (by
    change g.shift+g.scale • h.shift+(g.scale*h.scale) • k.shift =
      g.shift+g.scale • (h.shift+h.scale • k.shift)
    simp [mul_smul,smul_add,add_assoc])
  one_mul g := Hom.ext (one_mul _) (by change 0+(1 : ℝˣ) • g.shift = g.shift; simp)
  mul_one g := Hom.ext (mul_one _) (by change g.shift+g.scale • (0 : ℝ²) = g.shift; simp)
  inv_mul_cancel g := Hom.ext (inv_mul_cancel _) (by
    change -(g.scale⁻¹ • g.shift)+g.scale⁻¹ • g.shift = 0
    simp)

@[simp] theorem scale_mul (g h : Hom) : (g*h).scale = g.scale*h.scale := rfl
@[simp] theorem scale_one : (1 : Hom).scale = 1 := rfl
@[simp] theorem scale_inv (g : Hom) : g⁻¹.scale = g.scale⁻¹ := rfl
@[simp] theorem shift_one : (1 : Hom).shift = 0 := rfl

def Hom.act (g : Hom) (x : ℝ²) : ℝ² := g.shift+g.scale • x

open Hom

@[simp] theorem act_mul (g h : Hom) (x : ℝ²) : (g*h).act x = g.act (h.act x) := by
  change (g.shift+g.scale • h.shift)+(g.scale*h.scale) • x = _
  simp [act,smul_add,mul_smul,add_assoc]

@[simp] theorem act_one (x : ℝ²) : (1 : Hom).act x = x := by simp [act]

@[simp] theorem inv_act (g : Hom) (x : ℝ²) : g⁻¹.act (g.act x) = x := by
  rw [← act_mul,inv_mul_cancel,act_one]

@[simp] theorem act_inv (g : Hom) (x : ℝ²) : g.act (g⁻¹.act x) = x := by
  rw [← act_mul,mul_inv_cancel,act_one]

theorem act_injective (g : Hom) : Function.Injective g.act := by
  intro x y he
  simpa using congrArg g⁻¹.act he

def centered (s : ℝˣ) (p : ℝ²) : Hom := ⟨s,(1-(s : ℝ)) • p⟩

theorem centered_inj {s : ℝ² → ℝˣ} {S : Finset ℝ²} (hs : ∀ p ∈ S, s p ≠ 1) :
    (S : Set ℝ²).InjOn (fun p => centered (s p) p) := by
  intro p hp q hq he
  have h₁ : s p = s q := congrArg Hom.scale he
  have h₂ : (1-(s p : ℝ)) • p = (1-(s q : ℝ)) • q := congrArg Hom.shift he
  rw [← h₁] at h₂
  have hne : (s p : ℝ) ≠ 1 := fun hh => hs p hp (Units.ext hh)
  exact smul_right_injective ℝ² (sub_ne_zero.mpr hne.symm) h₂

/-- Among the maps based at a set in the original plane, prescribing one
input and one output leaves at most four possible centers. -/
theorem point_multiplicity (S : Finset ℝ²) (cap : NonCollinearFor 5 (S : Set ℝ²))
    (s : ℝ² → ℝˣ) (hs : ∀ p ∈ S, s p ≠ 1) (x y : ℝ²) :
    (S.filter (fun p => (centered (s p) p).act x = y)).card ≤ 4 := by
  by_contra! h
  obtain ⟨B,hB,hsize⟩ := Finset.exists_subset_card_eq (show 5 ≤ _ from h)
  have subs := hB.trans (Finset.filter_subset ..)
  apply cap (B : Set ℝ²) (Finset.coe_subset.mpr subs) B.finite_toSet (by simpa using hsize)
  apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
  refine ⟨x,y-x,?_⟩
  intro p hp
  have he := (Finset.mem_filter.mp (hB hp)).2
  have hn : (s p : ℝ) ≠ 1 := fun hh => hs p (subs hp) (Units.ext hh)
  have hc := sub_ne_zero.mpr hn.symm
  refine ⟨(1-(s p : ℝ))⁻¹,?_⟩
  change p = (1-(s p : ℝ))⁻¹ • (y-x)+x
  apply smul_right_injective ℝ² hc
  dsimp only
  rw [smul_add,smul_smul,mul_inv_cancel₀ hc,one_smul,← he]
  simp only [act,centered,Units.smul_def,sub_smul,one_smul]
  abel

theorem common_fixed_point {H : Finset Hom}
    (comm : ∀ g ∈ H, ∀ h ∈ H, g*h = h*g) {g : Hom} (hg : g ∈ H) (hn : g.scale ≠ 1) :
    ∃ x : ℝ², ∀ h ∈ H, h.act x = x := by
  have hs : (g.scale : ℝ) ≠ 1 := fun h => hn (Units.ext h)
  have hc := sub_ne_zero.mpr hs.symm
  let x := (1-(g.scale : ℝ))⁻¹ • g.shift
  have eqv (y : ℝ²) : g.act y = y ↔ (1-(g.scale : ℝ)) • y = g.shift := by
    simp only [act,Units.smul_def,sub_smul,one_smul,sub_eq_iff_eq_add]
    exact eq_comm
  have xfix : g.act x = x := (eqv x).mpr (by simp [x,smul_smul,hc])
  refine ⟨x,fun h hh => ?_⟩
  apply smul_right_injective ℝ² hc
  have hhit : g.act (h.act x) = h.act x := by rw [← act_mul,comm g hg h hh,act_mul,xfix]
  exact ((eqv _).mp hhit).trans ((eqv x).mp xfix).symm

def bracket (g h : Hom) := g*h*g⁻¹*h⁻¹

@[simp] theorem scale_bracket (g h : Hom) : (bracket g h).scale = 1 := by
  simp [bracket,mul_assoc]

theorem bracket_shift {g h : Hom} (hn : g*h ≠ h*g) : (bracket g h).shift ≠ 0 := by
  intro hz
  have he : bracket g h = 1 := Hom.ext (scale_bracket g h) hz
  change g*h*g⁻¹*h⁻¹ = 1 at he
  have hh := congrArg (fun z : Hom => z*h*g) he
  exact hn (by simpa [mul_assoc] using hh)

/-- Conjugating a pure translation rescales its translation vector. -/
theorem conjugate_act (k c : Hom) (hc : c.scale = 1) (x : ℝ²) :
    (k*c*k⁻¹).act x = k.scale • c.shift+x := by
  have ht : ∀ y : ℝ², c.act y = c.shift+y := fun y => by simp [act,hc]
  have hs : ∀ v y : ℝ², k.act (v+y) = k.scale • v+k.act y := fun v y => by
    simp [act,smul_add,add_left_comm]
  rw [act_mul,act_mul,ht,hs,← act_mul]
  simp

def orbit (A : Finset Hom) (a : Hom) (x : ℝ²) := A.image fun g => a.act (g.act x)

/-- The left translate permits a dense part of the original maps to lie in
a single coset of the finite set. The orbit points are counted in their
original affine chart. -/
theorem orbit_packing (H : Finset Hom) (invH : ∀ k ∈ H, k⁻¹ ∈ H)
    {g h : Hom} (hg : g ∈ H) (hh : h ∈ H) (hn : g*h ≠ h*g)
    (a : Hom) (x : ℝ²) (B : Finset ℝ²) (hB : B ⊆ orbit H a x)
    (cap : NonCollinearFor 5 (B : Set ℝ²)) :
    B.card*(H.image (fun k => (k.scale : ℝ))).card ≤ (H^7).card*4 := by
  let c := bracket g h
  have hc : c ∈ H^4 := by
    simpa only [bracket,c,pow_succ,pow_zero,one_mul] using
      Finset.mul_mem_mul (Finset.mul_mem_mul (Finset.mul_mem_mul hg hh) (invH g hg)) (invH h hh)
  have hd : a.scale • c.shift ≠ 0 := by
    intro h0
    exact bracket_shift hn ((MulAction.injective a.scale) (h0.trans (smul_zero _).symm))
  have packing := line_packing_into (A := B) (C := orbit (H^7) a x) cap
    (p := 0) hd (H.image (fun k => (k.scale : ℝ)))
  refine (packing ?_).trans (Nat.mul_le_mul_right _ Finset.card_image_le)
  intro b hb t ht
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (hB hb)
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp ht
  let w := k*c*k⁻¹*j
  have h5 : k*c ∈ H^5 := by simpa only [pow_succ' H 4] using Finset.mul_mem_mul hk hc
  have h6 : k*c*k⁻¹ ∈ H^6 := by simpa only [pow_succ H 5] using Finset.mul_mem_mul h5 (invH k hk)
  have hw : w ∈ H^7 := by simpa only [w,pow_succ H 6] using Finset.mul_mem_mul h6 hj
  refine Finset.mem_image.mpr ⟨w,hw,?_⟩
  change a.act ((k*c*k⁻¹*j).act x) = _
  rw [act_mul,conjugate_act k c (scale_bracket g h)]
  simp only [act,smul_add,zero_add,Units.smul_def,smul_smul]
  rw [mul_comm (a.scale : ℝ) (k.scale : ℝ)]
  abel

end Erdos101HomothetyOrbits

namespace Erdos101RichHomotheties

open EuclideanGeometry Erdos101HomothetyOrbits Erdos101ConicSecants Erdos101Parabola
  Erdos101OrderedGrid
open scoped Pointwise Classical

def matched (S : Finset ℝ²) (g : Hom) := S.filter fun x => g.act x ∈ S

def projected (f : ℝ² →ₗ[ℝ] ℝ) (g : Hom) : Mob := ⟨(g.scale : ℝ),f g.shift,0,1⟩

theorem projected_hit (f : ℝ² →ₗ[ℝ] ℝ) (g : Hom) (x : ℝ²) :
    (projected f g).hit (f x) (f (g.act x)) := by
  simp [projected,Mob.hit,Hom.act,Units.smul_def,add_comm]

theorem matched_graph (S : Finset ℝ²) (f : ℝ² →ₗ[ℝ] ℝ)
    (hf : (S : Set ℝ²).InjOn f) (g : Hom) :
    (matched S g).card ≤ (graph (S.image f) (projected f g)).card := by
  apply Finset.card_le_card_of_injOn (fun x => (f x,f (g.act x)))
  · intro x hx
    obtain ⟨hx,hy⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hx,Finset.mem_image_of_mem _ hy⟩,projected_hit f g x⟩
  · intro x hx y hy he
    exact hf (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 (congrArg Prod.fst he)

theorem quotient_overlap (S : Finset ℝ²) (g h : Hom) :
    (matched S g ∩ matched S h).card ≤ (matched S (g/h)).card := by
  apply Finset.card_le_card_of_injOn h.act
  · intro x hx
    obtain ⟨hg,hh⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hh).2,
      by simpa [div_eq_mul_inv] using (Finset.mem_filter.mp hg).2⟩
  · exact (act_injective h).injOn

theorem two_hits {g h : Hom} {f : ℝ² →ₗ[ℝ] ℝ} {x y z w : ℝ} (hx : x ≠ z)
    (g₁ : (projected f g).hit x y) (g₂ : (projected f g).hit z w)
    (h₁ : (projected f h).hit x y) (h₂ : (projected f h).hit z w) :
    g.scale = h.scale ∧ f g.shift = f h.shift := by
  simp only [projected,Mob.hit,zero_mul,zero_add,one_mul] at g₁ g₂ h₁ h₂
  have he : ((g.scale : ℝ)-(h.scale : ℝ))*(x-z) = 0 := by linarith only [g₁,g₂,h₁,h₂]
  have hs := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hx))
  exact ⟨Units.ext hs,by linarith only [g₁,h₁,congrArg (fun u : ℝ => u*x) hs]⟩

/-- A family of distinct homotheties each mapping at least `n/t` points
back into the same `n`-point set has size at most a constant times `n`. -/
theorem rich_count (S : Finset ℝ²) (A : Finset Hom) {t : ℕ} (ht : 0 < t)
    (hn : 64*t ≤ S.card) (hr : ∀ g ∈ A, S.card ≤ t*(matched S g).card) :
    A.card ≤ 8*t*(64*t)^8*S.card := by
  let U := S ∪ A.image Hom.shift
  obtain ⟨f,hf,_⟩ := Erdos101CentralMaps.generic_form U (fun _ => 2)
  have sub : S ⊆ U := Finset.subset_union_left
  have inj := hf.mono (Finset.coe_subset.mpr sub)
  let X := S.image f
  let G (g : Hom) := ranked X (projected f g)
  have hX : X.card ≤ S.card := Finset.card_image_le
  have det (g : Hom) : (projected f g).det ≠ 0 := by simp [projected,Mob.det]
  have sample (T : Finset Pos) (hT : T.card = 3) :
      (A.filter (fun g => T ⊆ G g)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro g hg h hh
    obtain ⟨hgA,hgT⟩ := Finset.mem_filter.mp hg
    obtain ⟨hhA,hhT⟩ := Finset.mem_filter.mp hh
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
    obtain ⟨p,hp,hpu⟩ := Finset.mem_image.mp (hgT hu)
    obtain ⟨q,hq,hqv⟩ := Finset.mem_image.mp (hgT hv)
    obtain ⟨hpX,hpg⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqX,hqg⟩ := Finset.mem_filter.mp hq
    have hne : p.1 ≠ q.1 := by
      intro h
      have he := Prod.ext h (Mob.hit_unique (det g) hpg (h ▸ hqg))
      exact huv (hpu.symm.trans ((congrArg (ranks X) he).trans hqv))
    obtain ⟨hs,hb⟩ := two_hits hne hpg hqg
      (hit_of_ranked hpX (hpu ▸ hhT hu)) (hit_of_ranked hqX (hqv ▸ hhT hv))
    exact Hom.ext hs (hf (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hgA))
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hhA)) hb)
  have hc := rich_graphs A G ht hn (fun g _ => ranked_subset X _ hX)
    (fun g _ => graph_two_chains X _ (det g)) (fun g hg => by
      dsimp [G]; rw [ranked_card]
      exact (hr g hg).trans (Nat.mul_le_mul_left t (matched_graph S f inj g))) sample
  simpa only [mul_one] using hc

def edges (S : Finset ℝ²) (F : Finset Hom) (β : ℝ) :=
  (F ×ˢ F).filter fun e => β*(S.card : ℝ) ≤ (matched S e.1 ∩ matched S e.2).card

theorem dense_quotients (S : Finset ℝ²) (F : Finset Hom) {α : ℝ} (hα : 0 < α)
    (hn : 0 < S.card) (hr : ∀ g ∈ F, α*(S.card : ℝ) ≤ (matched S g).card) :
    α^2/2*(F.card : ℝ)^2 ≤ (edges S F (α^2/2)).card := by
  let n : ℝ := S.card
  let m : ℝ := F.card
  let P := F ×ˢ F
  let I (e : Hom × Hom) := (matched S e.1 ∩ matched S e.2).card
  let E := edges S F (α^2/2)
  have hnR : 0 < n := Nat.cast_pos.mpr hn
  have ci := Erdos101SecantSamples.common_pivots F S (matched S)
    (fun g _ => Finset.filter_subset ..)
  have ciR : (∑ g ∈ F, ((matched S g).card : ℝ))^2 ≤ n*(∑ e ∈ P, (I e : ℝ)) := by
    have hh := (Nat.cast_le (α := ℝ)).mpr ci
    push_cast at hh
    exact hh
  have mass : m*(α*n) ≤ ∑ g ∈ F, ((matched S g).card : ℝ) := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hr
  have upper (e : Hom × Hom) (he : e ∈ P) :
      (I e : ℝ) ≤ α^2/2*n+(if e ∈ E then n else 0) := by
    by_cases h : e ∈ E
    · rw [if_pos h]
      have hi : (I e : ℝ) ≤ n := Nat.cast_le.mpr (Finset.card_le_card
        (Finset.inter_subset_left.trans (Finset.filter_subset ..)))
      exact hi.trans (le_add_of_nonneg_left (mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) hnR.le))
    · rw [if_neg h,add_zero]
      exact (lt_of_not_ge fun h' => h (Finset.mem_filter.mpr ⟨he,h'⟩)).le
  have esub : E ⊆ P := Finset.filter_subset ..
  have bound : ∑ e ∈ P, (I e : ℝ) ≤ m^2*(α^2/2*n)+(E.card : ℝ)*n := calc
    _ ≤ ∑ e ∈ P, (α^2/2*n+(if e ∈ E then n else 0)) := Finset.sum_le_sum upper
    _ = _ := by simp [Finset.sum_add_distrib,Finset.sum_ite_mem,P,m,pow_two,Finset.inter_eq_right.mpr esub]
  have tot := ((pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg F.card) (mul_pos hα hnR).le) mass 2).trans ciR).trans
    (mul_le_mul_of_nonneg_left bound hnR.le)
  refine le_of_mul_le_mul_right (a := n^2) ?_ (sq_pos_of_pos hnR)
  change α^2/2*m^2*n^2 ≤ (E.card : ℝ)*n^2
  nlinarith only [tot]

/-- The quotient graph of a family of rich maps has a dense edge set and
a linear number of distinct quotient labels. -/
theorem quotient_data (α : ℝ) (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ (S : Finset ℝ²) (F : Finset Hom),
      N ≤ S.card → α*(S.card : ℝ) ≤ F.card →
      (∀ g ∈ F, α*(S.card : ℝ) ≤ (matched S g).card) →
      ∃ (E : Finset (Hom × Hom)) (R : Finset Hom), E ⊆ F ×ˢ F ∧
        α^2/2*(F.card : ℝ)^2 ≤ E.card ∧ (∀ e ∈ E, e.1/e.2 ∈ R) ∧
        (R.card : ℝ) ≤ K*F.card := by
  let β := α^2/2
  have hβ : 0 < β := by dsimp [β]; positivity
  obtain ⟨t,ht⟩ := exists_nat_gt (1/β)
  have htR : (0 : ℝ) < t := (one_div_pos.mpr hβ).trans ht
  have ht0 : 0 < t := Nat.cast_pos.mp htR
  let C := 8*t*(64*t)^8
  have hC : (0 : ℝ) < C := Nat.cast_pos.mpr (by dsimp [C]; positivity)
  refine ⟨(C : ℝ)/α,div_pos hC hα,64*t,?_⟩
  intro S F hn hF hr
  let E := edges S F β
  let R := E.image fun e => e.1/e.2
  have hn0 : 0 < S.card := (Nat.mul_pos (by norm_num : 0 < 64) ht0).trans_le hn
  have rich (g : Hom) (hg : g ∈ R) : S.card ≤ t*(matched S g).card := by
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hg
    have hi : β*(S.card : ℝ) ≤ (matched S (e.1/e.2)).card :=
      (Finset.mem_filter.mp he).2.trans (Nat.cast_le.mpr (quotient_overlap ..))
    have hprod := (mul_le_mul_of_nonneg_left hi htR.le)
    have htime := (div_lt_iff₀ hβ).mp ht
    have hh : (S.card : ℝ) ≤ (t : ℝ)*(matched S (e.1/e.2)).card := by
      nlinarith only [hprod,mul_le_mul_of_nonneg_right htime.le (Nat.cast_nonneg S.card)]
    exact_mod_cast hh
  have count : (R.card : ℝ) ≤ (C : ℝ)*S.card := by exact_mod_cast rich_count S R ht0 hn rich
  refine ⟨E,R,Finset.filter_subset ..,dense_quotients S F hα hn0 hr,
    fun e he => Finset.mem_image_of_mem _ he,count.trans ?_⟩
  have hSc : (S.card : ℝ) ≤ F.card/α := (le_div_iff₀ hα).mpr (by simpa [mul_comm] using hF)
  calc
    _ ≤ (C : ℝ)*(F.card/α) := mul_le_mul_of_nonneg_left hSc hC.le
    _ = _ := by ring

end Erdos101RichHomotheties

namespace Erdos101PopularDifferences

open scoped Pointwise Classical

variable {G : Type*} [Group G] [DecidableEq G]

/-- Number of ordered words of length `m` over `D` whose product is `g`. -/
def words (D : Finset G) : ℕ → G → ℕ
  | 0,g => if g = 1 then 1 else 0
  | m+1,g => ∑ d ∈ D, words D m (d⁻¹*g)

theorem word_mass (D : Finset G) (m : ℕ) (T : Finset G) :
    ∑ g ∈ T, words D m g ≤ D.card^m := by
  induction m generalizing T with
  | zero =>
    by_cases h : (1 : G) ∈ T <;> simp [words,h]
  | succ m ih =>
    simp only [words,Finset.sum_comm (s := T) (t := D)]
    calc
      _ ≤ ∑ _d ∈ D, D.card^m := by
        apply Finset.sum_le_sum
        intro d hd
        have hi : Function.Injective (fun g : G => d⁻¹*g) := mul_right_injective _
        simpa only [Finset.sum_image hi.injOn] using ih (T.image (fun g => d⁻¹*g))
      _ = _ := by simp [pow_succ,mul_comm]

def sources (A : Finset G) (s : G) := A.filter fun b => b*s ∈ A

def rightDifferences (A : Finset G) : Finset G :=
  (A ×ˢ A).image fun e => e.1⁻¹*e.2

def popular (A : Finset G) (M : ℕ) :=
  (rightDifferences A).filter fun s => M ≤ (sources A s).card

theorem popular_inv (A : Finset G) (M : ℕ) {s : G} (hs : s ∈ popular A M) :
    s⁻¹ ∈ popular A M := by
  obtain ⟨hd,hr⟩ := Finset.mem_filter.mp hs
  obtain ⟨⟨p,q⟩,hpq,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(q,p),Finset.mem_product.mpr ⟨hq,hp⟩,by simp⟩,hr.trans ?_⟩
  apply Finset.card_le_card_of_injOn (fun x => x*(p⁻¹*q))
  · intro x hx
    obtain ⟨ha,hb⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hb,by simpa [mul_assoc] using ha⟩
  · exact (mul_left_injective _).injOn

/-- The second moment of the translates `a/A` forces many popular right
differences. The estimate retains the integer threshold explicitly. -/
theorem popular_card (A : Finset G) (M : ℕ) :
    A.card^2 ≤ (A/A).card*(M+(popular A M).card) := by
  by_cases hempty : A = ∅
  · simp [hempty]
  have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  let D (a : G) := A.image (fun c => a/c)
  have hcard (a : G) : (D a).card = A.card := Finset.card_image_of_injective _ div_right_injective
  have sub (a : G) (ha : a ∈ A) : D a ⊆ A/A := by
    rintro w hw
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hw
    exact Finset.div_mem_div ha hb
  have overlap (p q : G) : (D p ∩ D q).card ≤ (sources A (q⁻¹*p)).card := by
    apply Finset.card_le_card_of_injOn (fun w => w⁻¹*q)
    · intro w hw
      obtain ⟨hp,hq⟩ := Finset.mem_inter.mp hw
      obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hp
      obtain ⟨b,hb,he'⟩ := Finset.mem_image.mp hq
      apply Finset.mem_filter.mpr
      constructor
      · simpa [← he',div_eq_mul_inv,mul_assoc] using hb
      · simpa [← he,div_eq_mul_inv,mul_assoc] using ha
    · intro w hw v hv h
      exact inv_injective (mul_right_cancel h)
  let H := popular A M
  have each (e : G × G) (he : e ∈ A ×ˢ A) : (D e.1 ∩ D e.2).card ≤
      M + (if e.2⁻¹*e.1 ∈ H then A.card else 0) := by
    by_cases hh : e.2⁻¹*e.1 ∈ H
    · rw [if_pos hh]
      exact (Finset.card_le_card Finset.inter_subset_left).trans (hcard e.1 ▸ Nat.le_add_left _ _)
    · rw [if_neg hh,add_zero]
      apply (overlap ..).trans
      by_contra! ht
      exact hh (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨(e.2,e.1),Finset.mem_product.mpr ⟨(Finset.mem_product.mp he).2,(Finset.mem_product.mp he).1⟩,rfl⟩,ht.le⟩)
  let F := (A ×ˢ A).filter (fun e : G × G => e.2⁻¹*e.1 ∈ H)
  have hF : F.card ≤ H.card*A.card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun e : G × G => (e.2⁻¹*e.1,e.2))
    · intro e he
      exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp he).2,
        (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2⟩
    · rintro ⟨p,q⟩ hp ⟨p',q'⟩ hq hh
      obtain ⟨h₁,h₂⟩ := Prod.mk.inj hh
      change q = q' at h₂
      subst q'
      exact Prod.ext (mul_left_cancel h₁) rfl
  have total : ∑ e ∈ A ×ˢ A, (D e.1 ∩ D e.2).card ≤ A.card^2*(M+H.card) := calc
    _ ≤ ∑ e ∈ A ×ˢ A, (M + (if e.2⁻¹*e.1 ∈ H then A.card else 0)) := Finset.sum_le_sum each
    _ = A.card^2*M + F.card*A.card := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_product,nsmul_eq_mul,pow_two,
        F,← Finset.sum_filter,Nat.cast_id]
    _ ≤ _ := by nlinarith only [Nat.mul_le_mul_right A.card hF]
  have ci := Erdos101SecantSamples.common_pivots A (A/A) D sub
  simp_rw [hcard,Finset.sum_const,nsmul_eq_mul] at ci
  have h := ci.trans (Nat.mul_le_mul_left _ total)
  refine Nat.le_of_mul_le_mul_left (c := A.card^2) ?_ (pow_pos hpos _)
  simpa only [H,Nat.cast_id,pow_two,mul_assoc,mul_comm,mul_left_comm] using h

/-- Internal points may be chosen independently along a given word.
Their choices give distinct representations by successive differences. -/
theorem many_words (A H : Finset G) (M : ℕ) (rich : ∀ s ∈ H, M ≤ (sources A s).card)
    (m : ℕ) {a b w : G} (ha : a ∈ A) (hb : b ∈ A) (hw : w ∈ H^m) :
    M^m ≤ words (A/A) (m+1) (a*w/b) := by
  induction m generalizing a b w with
  | zero =>
    have he : w = 1 := by simpa using hw
    subst w
    have h := Finset.single_le_sum (s := A/A)
      (f := fun d : G => words (A/A) 0 (d⁻¹*(a/b)))
      (fun _ _ => Nat.zero_le _) (Finset.div_mem_div ha hb)
    simpa [words] using h
  | succ m ih =>
    rw [pow_succ'] at hw
    obtain ⟨s,hs,v,hv,rfl⟩ := Finset.mem_mul.mp hw
    let C := sources A s
    let D := C.image fun c => a/c
    have inject : Function.Injective (fun c : G => a/c) := div_right_injective
    have hd : D.card = C.card := Finset.card_image_of_injective _ inject
    have sub : D ⊆ A/A := by
      intro d h
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp h
      exact Finset.div_mem_div ha (Finset.mem_filter.mp hc).1
    have point (d : G) (hd' : d ∈ D) :
        M^m ≤ words (A/A) (m+1) (d⁻¹*(a*(s*v)/b)) := by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hd'
      have he : (a/c)⁻¹*(a*(s*v)/b) = (c*s)*v/b := by
        simp [div_eq_mul_inv,mul_assoc]
      rw [he]
      exact ih (Finset.mem_filter.mp hc).2 hb hv
    change M^(m+1) ≤ ∑ d ∈ A/A, words (A/A) (m+1) (d⁻¹*(a*(s*v)/b))
    calc
      _ = M*M^m := pow_succ' _ _
      _ ≤ D.card*M^m := Nat.mul_le_mul_right _ (hd ▸ rich s hs)
      _ = ∑ _d ∈ D, M^m := by simp
      _ ≤ ∑ d ∈ D, words (A/A) (m+1) (d⁻¹*(a*(s*v)/b)) := Finset.sum_le_sum point
      _ ≤ _ := Finset.sum_le_sum_of_subset sub

/-- A uniform bound for each fixed power of the popular differences. -/
theorem power_bound (A H : Finset G) (M : ℕ) (rich : ∀ s ∈ H, M ≤ (sources A s).card)
    (m : ℕ) : (A*H^m/A).card*M^m ≤ (A/A).card^(m+1) := by
  let X := A*H^m/A
  calc
    _ = ∑ _x ∈ X, M^m := by simp [X]
    _ ≤ ∑ x ∈ X, words (A/A) (m+1) x := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨c,hc,b,hb,rfl⟩ := Finset.mem_div.mp hx
      obtain ⟨a,ha,w,hw,rfl⟩ := Finset.mem_mul.mp hc
      exact many_words A H M rich m ha hb hw
    _ ≤ _ := word_mass (A/A) (m+1) X

/-- A coset of the popular differences captures many elements of the
original set. This follows by counting pairs `(a,s)` with `a*s ∈ A`. -/
theorem popular_translate (A : Finset G) (hA : A.Nonempty) (M : ℕ) :
    ∃ a ∈ A, M*(popular A M).card ≤ A.card*((popular A M).filter (fun s => a*s ∈ A)).card := by
  let H := popular A M
  let R (s a : G) := a*s ∈ A
  let count (a : G) := (H.bipartiteBelow R a).card
  obtain ⟨a,ha,hm⟩ := A.exists_max_image count hA
  refine ⟨a,ha,?_⟩
  calc
    _ = ∑ _s ∈ H, M := by simp [H,mul_comm]
    _ ≤ ∑ s ∈ H, (A.bipartiteAbove R s).card :=
      Finset.sum_le_sum fun s hs => (Finset.mem_filter.mp hs).2
    _ = ∑ p ∈ A, count p := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ..
    _ ≤ ∑ _p ∈ A, count a := Finset.sum_le_sum fun p hp => hm p hp
    _ = _ := by simp [count,H,Finset.bipartiteBelow,R]

theorem popular_power (A : Finset G) (hA : A.Nonempty) (M m : ℕ) :
    ((popular A M)^m).card*M^m ≤ (A/A).card^(m+1) := by
  obtain ⟨a,ha⟩ := hA
  let H := popular A M
  have sub : (H^m).card ≤ (A*H^m/A).card := by
    apply Finset.card_le_card_of_injOn (fun x => a*x/a)
    · exact fun x hx => Finset.div_mem_div (Finset.mul_mem_mul ha hx) ha
    · exact fun _ _ _ _ h => mul_left_cancel (div_left_inj.mp h)
  exact (Nat.mul_le_mul_right _ sub).trans
    (power_bound A H M (fun s hs => (Finset.mem_filter.mp hs).2) m)

def paths (A : Finset G) (E : Finset (G × G)) (a b : G) :=
  (A ×ˢ A).filter fun q : G × G => (a,q.1) ∈ E ∧ (q.2,q.1) ∈ E ∧ (q.2,b) ∈ E

def three (D : Finset G) (g : G) := (D ×ˢ D ×ˢ D).filter
  fun q : G × G × G => q.1/q.2.1*q.2.2 = g

theorem path_bound (A R : Finset G) (E : Finset (G × G))
    (hr : ∀ e ∈ E, e.1/e.2 ∈ R) (a b : G) :
    (paths A E a b).card ≤ (three R (a/b)).card := by
  apply Finset.card_le_card_of_injOn (fun q : G × G => (a/q.1,q.2/q.1,q.2/b))
  · intro q hq
    obtain ⟨_,h₁,h₂,h₃⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨hr _ h₁,Finset.mem_product.mpr ⟨hr _ h₂,hr _ h₃⟩⟩,?_⟩
    simp [div_eq_mul_inv,mul_assoc]
  · intro p hp q hq he
    exact Prod.ext (div_right_injective (congrArg Prod.fst he))
      (div_left_inj.mp (congrArg (fun e : G × G × G => e.2.2) he))

theorem three_total (R T : Finset G) : ∑ g ∈ T, (three R g).card ≤ R.card^3 := by
  unfold three
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simpa only [Finset.card_product,pow_succ,pow_zero,one_mul,mul_assoc] using
    Finset.card_le_card (Finset.filter_subset (fun q : G × G × G => q.1/q.2.1*q.2.2 ∈ T)
      (R ×ˢ R ×ˢ R))

/-- From many restricted quotients in a small set, extract many original
elements whose full quotient set is small. The graph rectangle is McKenna's
group-free dependent-random-choice lemma. -/
theorem restricted_quotients (δ K : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hK : 0 < K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (F R : Finset G) (E : Finset (G × G)),
      F.Nonempty → E ⊆ F ×ˢ F → δ*(F.card : ℝ)^2 ≤ E.card →
      (∀ e ∈ E, e.1/e.2 ∈ R) → (R.card : ℝ) ≤ K*F.card →
      ∃ A ⊆ F, c*(F.card : ℝ) ≤ A.card ∧ ((A/A).card : ℝ) ≤ C*F.card := by
  let c := δ/8
  let τ := δ^5/2^12
  let L := K^3/τ
  have hc : 0 < c := by dsimp [c]; positivity
  have ht : 0 < τ := by dsimp [τ]; positivity
  have hL : 0 < L := div_pos (pow_pos hK _) ht
  refine ⟨c,L^2/c,hc,div_pos (pow_pos hL _) hc,?_⟩
  intro F R E hF hE hden hr hsize
  have hn : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  obtain ⟨A,B,hA,hB,ha,hb,hpaths⟩ := Finset.graph_dependentRandomChoice_payoff_pointwise
    δ hδ hδ₁ F F hF rfl E hE (by simpa only [pow_two,mul_assoc] using hden)
  have per (g : G) (hg : g ∈ A/B) : τ*(F.card : ℝ)^2 ≤ (three R g).card := by
    obtain ⟨a,ha',b,hb',rfl⟩ := Finset.mem_div.mp hg
    exact (hpaths a ha' b hb').trans (Nat.cast_le.mpr (path_bound F R E hr a b))
  have count : ((A/B).card : ℝ)*(τ*(F.card : ℝ)^2) ≤ (R.card : ℝ)^3 := calc
    _ = ∑ _g ∈ A/B, τ*(F.card : ℝ)^2 := by simp
    _ ≤ ∑ g ∈ A/B, ((three R g).card : ℝ) := Finset.sum_le_sum per
    _ ≤ _ := by exact_mod_cast three_total R (A/B)
  have prodBound := count.trans (pow_le_pow_left₀ (by positivity) hsize 3)
  have hcross : ((A/B).card : ℝ) ≤ L*F.card := by
    apply le_of_mul_le_mul_right (a := τ*(F.card : ℝ)^2) _ (mul_pos ht (pow_pos hn _))
    calc
      _ ≤ _ := prodBound
      _ = _ := by dsimp [L]; field_simp
  have rz := Finset.ruzsa_triangle_inequality_div_div_div A B A
  have rzR : ((A/A).card : ℝ)*B.card ≤ ((A/B).card : ℝ)^2 := by
    exact_mod_cast (show (A/A).card*B.card ≤ (A/B).card^2 by simpa only [pow_two] using rz)
  refine ⟨A,hA,ha,?_⟩
  apply le_of_mul_le_mul_right (a := c*(F.card : ℝ)) _ (mul_pos hc hn)
  calc
    _ ≤ ((A/A).card : ℝ)*B.card := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ _ := rzR
    _ ≤ (L*F.card)^2 := pow_le_pow_left₀ (by positivity) hcross 2
    _ = _ := by field_simp

/-- The finite-power form of the noncommutative graph lemma. A positive
proportion of the original elements lie in one translate of a symmetric set
whose seventh power is still linear in the input cardinality. -/
theorem seven_products (δ K : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hK : 0 < K) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∃ N : ℕ, ∀ (F R : Finset G) (E : Finset (G × G)),
      N ≤ F.card → E ⊆ F ×ˢ F → δ*(F.card : ℝ)^2 ≤ E.card →
      (∀ e ∈ E, e.1/e.2 ∈ R) → (R.card : ℝ) ≤ K*F.card →
      ∃ (H T : Finset G) (a : G), (∀ g ∈ H, g⁻¹ ∈ H) ∧ T ⊆ F ∧
        (∀ g ∈ T, ∃ h ∈ H, a*h = g) ∧ η*(F.card : ℝ) ≤ T.card ∧
        ((H^7).card : ℝ) ≤ C*F.card := by
  obtain ⟨c,D,hc,hD,reg⟩ := restricted_quotients (G := G) δ K hδ hδ₁ hK
  let β := c^2/(4*D)
  have hβ : 0 < β := by dsimp [β]; positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (2/β)
  refine ⟨β^2/2,D^8/(β/2)^7,by positivity,by positivity,N,?_⟩
  intro F R E hF hE hdense hr hsize
  let n : ℝ := F.card
  have hn : 2/β < n := hN.trans_le (Nat.cast_le.mpr hF)
  have hn0 : 0 < n := (div_pos (by norm_num : (0 : ℝ) < 2) hβ).trans hn
  have hne : F.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hn0)
  obtain ⟨A,hAF,hA,hdiv⟩ := reg F R E hne hE hdense hr hsize
  have hApos : (0 : ℝ) < A.card := (mul_pos hc hn0).trans_le hA
  have hAne := Finset.card_pos.mp (by exact_mod_cast hApos : 0 < A.card)
  let M : ℕ := ⌊β*n⌋₊
  let H := popular A M
  have hM : (M : ℝ) ≤ β*n := Nat.floor_le (mul_pos hβ hn0).le
  have hM' : (β/2)*n ≤ (M : ℝ) := by
    have ht := (div_lt_iff₀ hβ).mp hn
    have hh : β*n < (M : ℝ)+1 := Nat.lt_floor_add_one _
    linarith
  have count : (A.card : ℝ)^2 ≤ ((A/A).card : ℝ)*((M : ℝ)+(H.card : ℝ)) := by
    exact_mod_cast popular_card A M
  have hident : c^2 = 4*D*β := by dsimp [β]; field_simp
  have hH : β*n ≤ (H.card : ℝ) := by
    have bound := (pow_le_pow_left₀ (mul_pos hc hn0).le hA 2).trans
      (count.trans (mul_le_mul_of_nonneg_right hdiv (add_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg H.card))))
    by_contra! hsmall
    have hsum : (M : ℝ)+H.card < 2*(β*n) := by linarith
    have silly := bound.trans_lt (mul_lt_mul_of_pos_left hsum (mul_pos hD hn0))
    nlinarith only [silly,congrArg (fun x : ℝ => x*n^2) hident,mul_pos (mul_pos hD hβ) (sq_pos_of_pos hn0)]
  obtain ⟨a,ha,hcount⟩ := popular_translate A hAne M
  let J := H.filter fun s => a*s ∈ A
  let T := J.image fun s => a*s
  have hT : T.card = J.card := Finset.card_image_of_injective _ (mul_right_injective a)
  have smallA : (A.card : ℝ) ≤ n := Nat.cast_le.mpr (Finset.card_le_card hAF)
  have capture : (M : ℝ)*H.card ≤ (A.card : ℝ)*J.card := by exact_mod_cast hcount
  refine ⟨H,T,a,fun _ hg => popular_inv A M hg,?_,?_,?_,?_⟩
  · intro g hg
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hg
    exact hAF (Finset.mem_filter.mp hs).2
  · intro g hg
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hg
    exact ⟨s,(Finset.mem_filter.mp hs).1,rfl⟩
  · rw [hT]
    refine le_of_mul_le_mul_right (a := n) ?_ hn0
    calc
      _ = (β/2*n)*(β*n) := by ring
      _ ≤ (M : ℝ)*H.card := mul_le_mul hM' hH (mul_pos hβ hn0).le (by positivity)
      _ ≤ _ := capture
      _ ≤ _ := by simpa only [mul_comm n] using mul_le_mul_of_nonneg_right smallA (Nat.cast_nonneg J.card)
  · have pb : ((H^7).card : ℝ)*(M : ℝ)^7 ≤ ((A/A).card : ℝ)^8 := by
      exact_mod_cast popular_power A hAne M 7
    refine le_of_mul_le_mul_right (a := ((β/2)*n)^7) ?_ (pow_pos (mul_pos (half_pos hβ) hn0) _)
    calc
      _ ≤ ((H^7).card : ℝ)*(M : ℝ)^7 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_pos (half_pos hβ) hn0).le hM' 7) (Nat.cast_nonneg (H^7).card)
      _ ≤ _ := pb
      _ ≤ (D*n)^8 := pow_le_pow_left₀ (Nat.cast_nonneg (A/A).card) hdiv 8
      _ = _ := by field_simp; rfl

end Erdos101PopularDifferences

namespace Erdos101CenterSparsity

open EuclideanGeometry Erdos101HomothetyOrbits Erdos101RichHomotheties
  Erdos101CentralMaps Erdos101PopularDifferences
open scoped Pointwise Classical

def family (S : Finset ℝ²) (s : ℝ² → ℝˣ) := S.image fun p => centered (s p) p

theorem eval_fiber (S : Finset ℝ²) (cap : NonCollinearFor 5 (S : Set ℝ²))
    (s : ℝ² → ℝˣ) (hs : ∀ p ∈ S, s p ≠ 1) (T : Finset Hom)
    (hT : T ⊆ family S s) (x y : ℝ²) : (T.filter (fun g => g.act x = y)).card ≤ 4 := by
  let P := S.filter fun p => (centered (s p) p).act x = y
  have sub : T.filter (fun g => g.act x = y) ⊆ P.image (fun p => centered (s p) p) := by
    intro g hg
    obtain ⟨hg,hit⟩ := Finset.mem_filter.mp hg
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hT hg)
    exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,hit⟩,rfl⟩
  exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans (point_multiplicity S cap s hs x y))

theorem large_orbit (S : Finset ℝ²) (cap : NonCollinearFor 5 (S : Set ℝ²))
    (hS : S.Nonempty) (s : ℝ² → ℝˣ) (hs : ∀ p ∈ S, s p ≠ 1) (T H : Finset Hom)
    (hT : T ⊆ family S s) (a : Hom) (coset : ∀ g ∈ T, ∃ h ∈ H, a*h = g)
    {α : ℝ} (rich : ∀ g ∈ T, α*(S.card : ℝ) ≤ (matched S g).card) :
    ∃ x ∈ S, ∃ B ⊆ S, B ⊆ orbit H a x ∧ α*(T.card : ℝ) ≤ 4*B.card := by
  let R (g : Hom) (x : ℝ²) := g.act x ∈ S
  let hits (x : ℝ²) := T.bipartiteBelow R x
  obtain ⟨x,hx,hmax⟩ := S.exists_max_image (fun x => (hits x).card) hS
  let U := hits x
  let B := U.image fun g => g.act x
  have mass : (T.card : ℝ)*(α*S.card) ≤ (S.card : ℝ)*U.card := calc
    _ = ∑ _g ∈ T, α*(S.card : ℝ) := by simp
    _ ≤ ∑ g ∈ T, ((matched S g).card : ℝ) := Finset.sum_le_sum rich
    _ = ∑ z ∈ S, ((hits z).card : ℝ) := by
      exact_mod_cast (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := T) (t := S) R)
    _ ≤ ∑ _z ∈ S, (U.card : ℝ) := Finset.sum_le_sum fun z hz => Nat.cast_le.mpr (hmax z hz)
    _ = _ := by simp
  have count : U.card ≤ B.card*4 := calc
    _ = _ := Finset.card_eq_sum_card_fiberwise (s := U) (t := B) (f := fun g => g.act x)
      (fun g hg => Finset.mem_image_of_mem _ hg)
    _ ≤ ∑ _y ∈ B, 4 := Finset.sum_le_sum (fun y _ => eval_fiber S cap s hs U
      ((Finset.filter_subset ..).trans hT) x y)
    _ = _ := by simp
  refine ⟨x,hx,B,?_,?_,?_⟩
  · intro y hy
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hg).2
  · intro y hy
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k,hk,rfl⟩ := coset _ (Finset.mem_filter.mp hg).1
    exact Finset.mem_image.mpr ⟨k,hk,(act_mul a k x).symm⟩
  · have hn : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
    have intermediate : α*(T.card : ℝ) ≤ U.card := by
      refine le_of_mul_le_mul_right (a := (S.card : ℝ)) ?_ hn
      linarith only [mass]
    exact intermediate.trans (by exact_mod_cast (count.trans_eq (Nat.mul_comm _ _)))

def scales (T : Finset Hom) := T.image fun g => (g.scale : ℝ)

theorem coset_scales (H T : Finset Hom) (a : Hom)
    (coset : ∀ g ∈ T, ∃ h ∈ H, a*h = g) : (scales T).card ≤ (scales H).card := by
  have sub : scales T ⊆ (scales H).image (fun r => (a.scale : ℝ)*r) := by
    intro r hr
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨h,hh,rfl⟩ := coset g hg
    exact Finset.mem_image.mpr ⟨_,Finset.mem_image_of_mem _ hh,rfl⟩
  exact (Finset.card_le_card sub).trans Finset.card_image_le

/-- A commuting family has a single scale or a common input-output pair.
In the other case the seventh-power orbit bounds its number of scales. -/
theorem few_scales (S : Finset ℝ²) (cap : NonCollinearFor 5 (S : Set ℝ²))
    (hS : S.Nonempty) (s : ℝ² → ℝˣ) (hs : ∀ p ∈ S, s p ≠ 1) (T H : Finset Hom)
    (hT : T ⊆ family S s) (a : Hom) (coset : ∀ g ∈ T, ∃ h ∈ H, a*h = g)
    (invH : ∀ g ∈ H, g⁻¹ ∈ H) {α : ℝ}
    (rich : ∀ g ∈ T, α*(S.card : ℝ) ≤ (matched S g).card) :
    (scales T).card ≤ 4 ∨
      α*T.card*(scales T).card ≤ 16*((H^7).card : ℝ) := by
  by_cases comm : ∀ g ∈ H, ∀ h ∈ H, g*h = h*g
  · left
    by_cases one : ∀ g ∈ H, g.scale = 1
    · have sub : scales H ⊆ {1} := by
        intro r hr
        obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hr
        simp [one g hg]
      exact (coset_scales H T a coset).trans ((Finset.card_le_card sub).trans (by simp))
    · push Not at one
      obtain ⟨g,hg,hn⟩ := one
      obtain ⟨x,hx⟩ := common_fixed_point comm hg hn
      have he : T.filter (fun g => g.act x = a.act x) = T := Finset.filter_eq_self.mpr (by
        intro b hb
        obtain ⟨h,hh,rfl⟩ := coset b hb
        rw [act_mul,hx h hh])
      exact Finset.card_image_le.trans (he ▸ eval_fiber S cap s hs T hT x (a.act x))
  · right
    push Not at comm
    obtain ⟨g,hg,h,hh,hn⟩ := comm
    obtain ⟨x,hx,B,hBS,hBO,hB⟩ := large_orbit S cap hS s hs T H hT a coset rich
    have pack := orbit_packing H invH hg hh hn a x B hBO
      (NonCollinearFor.subset (Finset.coe_subset.mpr hBS) cap)
    have packR : (B.card : ℝ)*(scales H).card ≤ ((H^7).card : ℝ)*4 := by exact_mod_cast pack
    calc
      _ ≤ (4*(B.card : ℝ))*(scales H).card := mul_le_mul hB
        (Nat.cast_le.mpr (coset_scales H T a coset)) (Nat.cast_nonneg _) (by positivity)
      _ ≤ _ := by linarith only [packR]

theorem mode (T : Finset Hom) (hn : T.Nonempty) :
    ∃ r ∈ scales T, T.card ≤ (scales T).card*(T.filter (fun g => (g.scale : ℝ) = r)).card := by
  let d (r : ℝ) := (T.filter (fun g => (g.scale : ℝ) = r)).card
  obtain ⟨r,hr,hm⟩ := (scales T).exists_max_image d (hn.image _)
  refine ⟨r,hr,?_⟩
  calc
    _ = ∑ v ∈ scales T, d v := Finset.card_eq_sum_card_fiberwise
      (fun g hg => Finset.mem_image_of_mem (fun h : Hom => (h.scale : ℝ)) hg)
    _ ≤ ∑ _v ∈ scales T, d r := Finset.sum_le_sum hm
    _ = _ := by simp [d]

/-- If a positive fraction of the centers each give linearly many matches,
one scale alone must occur at a positive fraction of the centers. -/
theorem large_scale_class (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ N : ℕ, ∀ (S I : Finset ℝ²) (s : ℝ² → ℝˣ),
      N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) → I ⊆ S →
      (∀ p ∈ S, s p ≠ 1) → α*(S.card : ℝ) ≤ I.card →
      (∀ p ∈ I, α*(S.card : ℝ) ≤ (matched S (centered (s p) p)).card) →
      ∃ r : ℝ, ζ*(S.card : ℝ) ≤ (I.filter (fun p => (s p : ℝ) = r)).card := by
  obtain ⟨K,hK,N₁,quotients⟩ := quotient_data α hα
  have hδ : 0 < α^2/2 := by positivity
  have hδ₁ : α^2/2 ≤ 1 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hα₁) hα.le,hα₁]
  obtain ⟨η,C,hη,hC,N₂,structure_bound⟩ := seven_products (G := Hom) (α^2/2) K hδ hδ₁ hK
  let d := η*α
  have hd : 0 < d := mul_pos hη hα
  let L := 4+16*C/(α*d)
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨M,hM⟩ := exists_nat_gt ((N₂+1 : ℝ)/α)
  refine ⟨d/L,div_pos hd hL,max N₁ M,?_⟩
  intro S I s hn cap hI hs hIsize hr
  let F := family I s
  have FI : F.card = I.card := Finset.card_image_of_injOn
    ((centered_inj hs).mono (Finset.coe_subset.mpr hI))
  have Fs : F ⊆ family S s := Finset.image_subset_image hI
  have Fsize : α*(S.card : ℝ) ≤ F.card := FI ▸ hIsize
  have Rg (g : Hom) (hg : g ∈ F) : α*(S.card : ℝ) ≤ (matched S g).card := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hg
    exact hr _ hp
  obtain ⟨E,R,hE,dense,rel,hR⟩ := quotients S F ((le_max_left ..).trans hn) Fsize Rg
  have hM' := (div_lt_iff₀ hα).mp (hM.trans_le (Nat.cast_le.mpr ((le_max_right ..).trans hn)))
  have hFN : N₂ ≤ F.card := by
    exact_mod_cast (show (N₂ : ℝ) ≤ (F.card : ℝ) by linarith only [hM',Fsize])
  have hn0 : (0 : ℝ) < S.card := by
    by_contra! h
    linarith only [hM',mul_nonpos_of_nonpos_of_nonneg h hα.le,(Nat.cast_nonneg N₂ : 0 ≤ (N₂ : ℝ))]
  obtain ⟨H,T,a,invH,hTF,coset,hT,powers⟩ := structure_bound F R E hFN hE dense rel hR
  have Fsmax : (F.card : ℝ) ≤ S.card := Nat.cast_le.mpr (FI ▸ Finset.card_le_card hI)
  have tsize : d*(S.card : ℝ) ≤ T.card := calc
    _ = η*(α*S.card) := by simp [d,mul_assoc]
    _ ≤ _ := (mul_le_mul_of_nonneg_left Fsize hη.le).trans hT
  have hT0 := (mul_pos hd hn0).trans_le tsize
  have power : ((H^7).card : ℝ) ≤ C*S.card := powers.trans (mul_le_mul_of_nonneg_left Fsmax hC.le)
  have alt := few_scales S cap (Finset.card_pos.mp (Nat.cast_pos.mp hn0)) s hs T H
    (hTF.trans Fs) a coset invH (fun g hg => Rg g (hTF hg))
  have slopes : ((scales T).card : ℝ) ≤ L := by
    rcases alt with small | bound
    · have hh : ((scales T).card : ℝ) ≤ 4 := by exact_mod_cast small
      exact hh.trans (le_add_of_nonneg_right (div_nonneg (by positivity) (mul_pos hα hd).le))
    · apply le_trans (b := 16*C/(α*d)) _ (le_add_of_nonneg_left (by norm_num))
      apply (le_div_iff₀ (mul_pos hα hd)).mpr
      refine le_of_mul_le_mul_right (a := (S.card : ℝ)) ?_ hn0
      calc
        _ = (α*(d*(S.card : ℝ)))*(scales T).card := by ring
        _ ≤ α*T.card*(scales T).card := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left tsize hα.le) (Nat.cast_nonneg _)
        _ ≤ _ := bound
        _ ≤ _ := by linarith only [power]
  obtain ⟨r,hr',hm⟩ := mode T (Finset.card_pos.mp (Nat.cast_pos.mp hT0))
  let P := I.filter (fun p => (s p : ℝ) = r)
  have sub : T.filter (fun g => (g.scale : ℝ) = r) ⊆ family P s := by
    intro g hg
    obtain ⟨hg,he⟩ := Finset.mem_filter.mp hg
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hTF hg)
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hp,he⟩)
  have hm' := hm.trans (Nat.mul_le_mul_left _ ((Finset.card_le_card sub).trans Finset.card_image_le))
  have hmR : (T.card : ℝ) ≤ (scales T).card*(P.card : ℝ) := by exact_mod_cast hm'
  have total := tsize.trans (hmR.trans (mul_le_mul_of_nonneg_right slopes (Nat.cast_nonneg P.card)))
  refine ⟨r,le_of_mul_le_mul_right (a := L) ?_ hL⟩
  calc
    _ = d*(S.card : ℝ) := by field_simp
    _ ≤ _ := by simpa only [mul_comm L] using total

end Erdos101CenterSparsity

namespace Erdos101IncidenceProjection

open EuclideanGeometry Erdos101.DivisionRatios
open scoped Classical

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def coordinates (f g : V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] ℝ² where
  toFun x := !₂[f x,g x]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp

theorem finite_projection (S : Finset V) : ∃ L : V →ₗ[ℝ] ℝ²,
    (S : Set V).InjOn L ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y →
      L z ∈ line[ℝ,L x,L y] → z ∈ line[ℝ,x,y] := by
  obtain ⟨f,hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    (fun p : S.offDiag => p.val.1-p.val.2)
    (fun p => sub_ne_zero.mpr (Finset.mem_offDiag.mp p.property).2.2)
  have inj : (S : Set V).InjOn f := by
    intro x hx y hy eq
    by_contra ne
    exact hf ⟨(x,y),Finset.mem_offDiag.mpr ⟨hx,hy,ne⟩⟩ (by simp [eq])
  let D (x y z : V) := (f y-f x) • (z-x)-(f z-f x) • (y-x)
  let W := ((S ×ˢ S ×ˢ S).image fun e => D e.1 e.2.1 e.2.2).erase 0
  obtain ⟨g,hg⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    (fun w : W => w.val) (fun w => (Finset.mem_erase.mp w.property).1)
  let L := coordinates f g
  refine ⟨L,fun x hx y hy he => inj hx hy (congrArg (fun p : ℝ² => p 0) he),?_⟩
  intro x hx y hy z hz hxy hline
  obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline
  rw [AffineMap.lineMap_apply_module] at ht
  have h₀ := congrArg (fun p : ℝ² => p 0) ht
  have h₁ := congrArg (fun p : ℝ² => p 1) ht
  change (1-t)*f x+t*f y = f z at h₀
  change (1-t)*g x+t*g y = g z at h₁
  have v₀ : f z-f x = t*(f y-f x) := by linarith only [h₀]
  have v₁ : g z-g x = t*(g y-g x) := by linarith only [h₁]
  have zero : D x y z = 0 := by
    by_contra bad
    apply hg ⟨D x y z,Finset.mem_erase.mpr ⟨bad,Finset.mem_image.mpr
      ⟨(x,y,z),Finset.mem_product.mpr ⟨hx,Finset.mem_product.mpr ⟨hy,hz⟩⟩,rfl⟩⟩⟩
    change g (D x y z) = 0
    simp only [D,map_sub,map_smul,smul_eq_mul,v₀,v₁]
    ring
  have hn : f y-f x ≠ 0 := sub_ne_zero.mpr (fun e => hxy (inj hy hx e).symm)
  have he := sub_eq_zero.mp zero
  rw [v₀,mul_comm t,← smul_smul] at he
  have h := smul_right_injective V hn he
  exact mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨t,by
    simpa only [AffineMap.lineMap_apply_module',vadd_eq_add] using (eq_sub_iff_add_eq.mp h.symm)⟩

theorem cap_projection (S : Finset V) (cap : NoFiveCollinear (S : Set V)) :
    ∃ L : V →ₗ[ℝ] ℝ², (S : Set V).InjOn L ∧ NonCollinearFor 5 (S.image L : Set ℝ²) := by
  obtain ⟨L,inj,lines⟩ := finite_projection S
  refine ⟨L,inj,?_⟩
  intro A hA fin size col
  let Q := S.filter fun x => L x ∈ A
  have incl : Q ⊆ S := Finset.filter_subset ..
  have im : Q.image L = fin.toFinset := by
    ext p
    rw [fin.mem_toFinset]
    constructor
    · rintro hp
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
      exact (Finset.mem_filter.mp hx).2
    · intro hp
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (hA hp)
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hp⟩,rfl⟩
  have qsize : Q.card = 5 := calc
    Q.card = (Q.image L).card := (Finset.card_image_of_injOn (inj.mono (Finset.coe_subset.mpr incl))).symm
    _ = fin.toFinset.card := congrArg Finset.card im
    _ = 5 := (Set.ncard_eq_toFinset_card A fin).symm.trans size
  obtain ⟨x,y,hx,hy,ne⟩ := Finset.one_lt_card_iff.mp (show 1 < Q.card by omega)
  apply cap (Q : Set V) (Finset.coe_subset.mpr incl) Q.finite_toSet (by simpa using qsize)
  apply (collinear_iff_of_mem hx).mpr
  refine ⟨y-x,?_⟩
  intro z hz
  have proj := col.mem_affineSpan_of_mem_of_ne (Finset.mem_filter.mp hx).2
    (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2 (fun e => ne (inj (incl hx) (incl hy) e))
  obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
    (lines x (incl hx) y (incl hy) z (incl hz) ne proj)
  exact ⟨t,by simpa only [AffineMap.lineMap_apply_module',vadd_eq_add] using ht.symm⟩

end Erdos101IncidenceProjection

namespace Erdos101LiftedScaleClasses

open EuclideanGeometry SimpleGraph.TripartiteFromTriangles Erdos101.ProjectiveSums
  Erdos101CenterSparsity Erdos101RichHomotheties Erdos101HomothetyOrbits
open scoped Classical

section Rows

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def row (T : Finset (ι × ι × ι)) (p : ι) := T.filter fun e => e.1 = p

theorem row_bound (T : Finset (ι × ι × ι)) (hd : ExplicitDisjoint T) (p : ι) :
    (row T p).card ≤ Fintype.card ι := by
  apply Finset.card_le_card_of_injOn (t := Finset.univ) (fun e => e.2.1) (by simp)
  rintro ⟨x,y,z⟩ hx ⟨x',y',z'⟩ hx' e
  obtain ⟨ht,rfl⟩ := Finset.mem_filter.mp hx
  obtain ⟨ht',e'⟩ := Finset.mem_filter.mp hx'
  change x' = x at e'
  change y = y' at e
  subst x'; subst y'
  exact congrArg (fun a => (x,y,a)) (hd.inj₂ ht ht')

theorem dense_rows (T : Finset (ι × ι × ι)) (hd : ExplicitDisjoint T)
    {α : ℝ} (hα : 0 < α) (hn : 0 < Fintype.card ι)
    (dense : 2*α*(Fintype.card ι : ℝ)^2 ≤ T.card) :
    ∃ I : Finset ι, α*(Fintype.card ι : ℝ) ≤ I.card ∧
      ∀ x ∈ I, α*(Fintype.card ι : ℝ) ≤ (row T x).card := by
  let n : ℝ := Fintype.card ι
  let I := Finset.univ.filter fun p => α*n ≤ (row T p).card
  have hnR : 0 < n := Nat.cast_pos.mpr hn
  have total : (T.card : ℝ) = ∑ p : ι, ((row T p).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (s := T) (t := Finset.univ)
      (f := fun e => e.1) (by simp)
  have ub (p : ι) : ((row T p).card : ℝ) ≤ α*n+(if p ∈ I then n else 0) := by
    by_cases hp : p ∈ I
    · rw [if_pos hp]
      exact (Nat.cast_le.mpr (row_bound T hd p)).trans (le_add_of_nonneg_left (mul_pos hα hnR).le)
    · rw [if_neg hp,add_zero]
      exact (lt_of_not_ge (fun h => hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))).le
  have upper : (T.card : ℝ) ≤ n*(α*n)+(I.card : ℝ)*n := calc
    _ = _ := total
    _ ≤ ∑ p : ι, (α*n+(if p ∈ I then n else 0)) := Finset.sum_le_sum fun p _ => ub p
    _ = _ := by simp [Finset.sum_add_distrib,Finset.sum_ite_mem,n]
  refine ⟨I,le_of_mul_le_mul_right (a := n) ?_ hnR,fun p hp => (Finset.mem_filter.mp hp).2⟩
  change 2*α*n^2 ≤ T.card at dense
  nlinarith only [dense,upper]

omit [Fintype ι] in
theorem union_row_count (T : Finset (ι × ι × ι)) (K : Finset ι) (a : ℝ)
    (lower : ∀ p ∈ K, a ≤ (row T p).card) :
    (K.card : ℝ)*a ≤ (T.filter (fun e => e.1 ∈ K)).card := by
  calc
    _ = ∑ _p ∈ K, a := by simp
    _ ≤ ∑ p ∈ K, ((row T p).card : ℝ) := Finset.sum_le_sum lower
    _ = _ := by exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter (s := T) (t := K) (g := fun e => e.1)

end Rows

theorem concentration : OMA.R_Erdos101_erdos_101_R2_H1_R1.H2 := by
  intro ρ hρ
  let α := min (ρ/2) (1/2)
  have hα : 0 < α := lt_min (half_pos hρ) (by norm_num)
  have hα₁ : α ≤ 1 := (min_le_right ..).trans (by norm_num)
  obtain ⟨ζ,hζ,N,classes⟩ := large_scale_class α hα hα₁
  refine ⟨ζ*α,mul_pos hζ hα,max N 1,?_⟩
  intro S hn cap T hd size h s hs weight
  have hn0 : 0 < S.card := (le_max_right ..).trans hn
  have hnR : (0 : ℝ) < S.card := Nat.cast_pos.mpr hn0
  have ha : 2*α ≤ ρ := by linarith only [show α ≤ ρ/2 from min_le_left ..]
  obtain ⟨I,large,rich⟩ := dense_rows T hd hα (by simpa using hn0) (by
    simpa using (mul_le_mul_of_nonneg_right ha (sq_nonneg (S.card : ℝ))).trans size)
  let A := S.image (lift h)
  obtain ⟨L,linj,capP⟩ := Erdos101IncidenceProjection.cap_projection A (lift_no_five cap h)
  let v (p : ℝ²) := L (lift h p)
  let P := A.image L
  let w (p : S) := v p
  have vmem (p : ℝ²) (hp : p ∈ S) : v p ∈ P := Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hp)
  have vinj : (S : Set ℝ²).InjOn v := fun x hx y hy e => lift_injective h
    (linj (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hy) e)
  have winj : Function.Injective w := fun p q e => Subtype.ext (vinj p.property q.property e)
  have ps : P.card = S.card := (Finset.card_image_of_injOn linj).trans
    (Finset.card_image_of_injective S (lift_injective h))
  let t (q : ℝ²) := s (Function.invFunOn v (S : Set ℝ²) q)
  have tval (p : ℝ²) (hp : p ∈ S) : t (v p) = s p := congrArg s (vinj.leftInvOn_invFunOn hp)
  have hvalid (q : ℝ²) (hq : q ∈ P) : t q ≠ 1 := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    exact (tval p hp).symm ▸ hs p hp
  have hits (e : S × S × S) (he : e ∈ T) :
      w e.2.2 = (centered (t (w e.1)) (w e.1)).act (w e.2.1) := by
    have hh := congrArg L (weight e he)
    change L (lift h e.2.2) = L ((1-(s e.1 : ℝ)) • lift h e.1 + (s e.1 : ℝ) • lift h e.2.1) at hh
    simpa only [w,v,Hom.act,centered,Units.smul_def,tval _ e.1.property,map_add,map_smul] using hh
  let J := I.image w
  have sub (q : ℝ²) (hq : q ∈ J) : q ∈ P := by
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hq
    exact vmem _ x.property
  have jsize : α*(P.card : ℝ) ≤ J.card := by
    rw [ps,Finset.card_image_of_injective I winj]
    simpa using large
  have jrich (q : ℝ²) (hq : q ∈ J) : α*(P.card : ℝ) ≤ (matched P (centered (t q) q)).card := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    have lift_count : (row T x).card ≤ (matched P (centered (t (w x)) (w x))).card := by
      apply Finset.card_le_card_of_injOn (fun e => w e.2.1)
      · intro e he
        obtain ⟨heT,hx'⟩ := Finset.mem_filter.mp he
        refine Finset.mem_filter.mpr ⟨vmem _ e.2.1.property,?_⟩
        rw [← hx',← hits e heT]
        exact vmem _ e.2.2.property
      · rintro ⟨p,y,z⟩ he ⟨p',y',z'⟩ he' e
        obtain ⟨ht,hp⟩ := Finset.mem_filter.mp he
        obtain ⟨ht',hp'⟩ := Finset.mem_filter.mp he'
        change p = x at hp
        change p' = x at hp'
        subst p; subst p'
        have hyy : y = y' := winj e
        subst y'
        exact congrArg (fun a => (x,y,a)) (hd.inj₂ ht ht')
    rw [ps]
    exact (show α*(S.card : ℝ) ≤ (row T x).card by simpa using rich x hx).trans (Nat.cast_le.mpr lift_count)
  obtain ⟨r,hr⟩ := classes P J t (ps ▸ (le_max_left ..).trans hn) capP sub hvalid jsize jrich
  let K : Finset S := I.filter fun x : S => (s x : ℝ) = r
  have ksub : K ⊆ I := Finset.filter_subset ..
  have incl : J.filter (fun q => (t q : ℝ) = r) ⊆ K.image w := by
    intro q hq
    obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx,(tval x x.property) ▸ he⟩)
  have lower : ζ*(S.card : ℝ) ≤ K.card := by
    rw [←ps]
    exact hr.trans (Nat.cast_le.mpr ((Finset.card_le_card incl).trans Finset.card_image_le))
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (Nat.cast_pos.mp ((mul_pos hζ hnR).trans_le lower))
  refine ⟨s x,hs x x.property,T.filter (fun e => e.1 ∈ K),Finset.filter_subset ..,?_,?_⟩
  · calc
      _ = (ζ*(S.card : ℝ))*(α*S.card) := by ring
      _ ≤ (K.card : ℝ)*(α*S.card) := mul_le_mul_of_nonneg_right lower (mul_pos hα hnR).le
      _ ≤ _ := union_row_count T K _ (fun p hp => by simpa using rich p (ksub hp))
  · intro e he
    apply Units.ext
    have scale (p : S) (hp : p ∈ K) : (s p : ℝ) = r := (Finset.mem_filter.mp hp).2
    exact (scale e.1 (Finset.mem_filter.mp he).2).trans (scale x hx).symm

end Erdos101LiftedScaleClasses

theorem OMA.solution : OMA.R_Erdos101_erdos_101_R2_H1_R1.H2 :=
  Erdos101LiftedScaleClasses.concentration
