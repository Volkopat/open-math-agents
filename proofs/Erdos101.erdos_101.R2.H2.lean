import OMAReductions.R_Erdos101_erdos_101_R2
import Mathlib

-- Proof of the bounded triangle-ratio step for Erdős 101.
-- The additive-growth, projective-lift, and triangle-ratio arguments are by @ubuwaits.
-- The direct popular-difference argument for restricted sums is by @yves-pires.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


/-!
# Dependent random choice

The two dependent-random-choice lemmas below are adapted from Adam McKenna's
LeanFormalizations.Combinatorics.Additive.BalogSzemerediGowers at commit
db02244c25aecd74eb96d9186c922387824c1258. The original license follows.

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
**Markov refinement helper.** Given `U` and a bad-pair count bound
`#{(a, a') ∈ U×U : codeg_E(a, a') < τ} ≤ κ · |U|²`, produce
`A' ⊆ U` with `|A'| ≥ |U|/2` (when `κ ≤ 1/4`) such that for every
`a ∈ A'` the bad-partner count `#{a' ∈ U : codeg_E(a, a') < τ}` is
`≤ 2κ · |U|`.  Used inside `graph_dependentRandomChoice_payoff_pointwise_witness` with
`κ := δ/16`, giving `2κ = δ/8`.
-/
lemma graph_dependentRandomChoice_markov_refinement {G : Type*} [DecidableEq G]
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

/-- A run of equally spaced points in the double sumset produces translates
of the original set in the triple sumset, with multiplicity at most four. -/
private theorem progression_packing {A : Finset E} (hA : NoFiveCollinear (A : Set E))
    {p d : E} (hd : d ≠ 0) {m : ℕ}
    (hprog : ∀ i < m, p + i • d ∈ A + A) :
    A.card * m ≤ (A + A + A).card * 4 := by
  classical
  let P := A ×ˢ Finset.range m
  let f : E × ℕ → E := fun t => (p + t.2 • d) + t.1
  have hmaps : (P : Set (E × ℕ)).MapsTo f (A + A + A : Finset E) := by
    intro t ht
    obtain ⟨ha, hi⟩ := Finset.mem_product.mp ht
    exact Finset.add_mem_add (hprog t.2 (Finset.mem_range.mp hi)) ha
  have hcount (z : E) : (P.filter (fun t => f t = z)).card ≤ 4 := by
    let T := P.filter (fun t => f t = z)
    have hinj : (T : Set (E × ℕ)).InjOn Prod.fst := by
      rintro ⟨a, i⟩ hi ⟨b, j⟩ hj hab
      change a = b at hab
      subst b
      have heq := (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
      change p + i • d + a = p + j • d + a at heq
      have hsmul := add_left_cancel (add_right_cancel heq)
      rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ] at hsmul
      have hreal := (smul_left_injective ℝ hd) hsmul
      have hij : i = j := by exact_mod_cast hreal
      simp [hij]
    change T.card ≤ 4
    rw [← Finset.card_image_of_injOn hinj]
    apply card_le_four hA
    · intro a ha
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1
    · rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨z - p, d, ?_⟩
      intro a ha
      obtain ⟨⟨b, i⟩, ht, rfl⟩ := Finset.mem_image.mp ha
      refine ⟨-(i : ℝ), ?_⟩
      have heq := (Finset.mem_filter.mp ht).2
      change p + i • d + b = z at heq
      change b = -(i : ℝ) • d + (z - p)
      rw [neg_smul, Nat.cast_smul_eq_nsmul, ← heq]
      abel
  calc
    A.card * m = P.card := by simp [P]
    _ = _ := Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _z ∈ A + A + A, 4 := Finset.sum_le_sum (fun z _ => hcount z)
    _ = _ := by simp

omit [Module ℝ E] in
/-- Every starting point exits after at most `m` steps. Recording the first exit
and its index bounds the size of the set by the size of its new boundary. -/
private theorem translate_growth {Y : Finset E} {d : E} {m : ℕ}
    (hexit : ∀ y ∈ Y, ∃ j < m, y + j • d ∉ Y) :
    m * Y.card + Y.card ≤ m * (Y ∪ Y.image (· + d)).card := by
  classical
  let boundary := Y.image (· + d) \ Y
  have hfirst (y : E) (hy : y ∈ Y) :
      ∃ j < m, y + j • d ∈ boundary := by
    obtain ⟨j, hj, hout⟩ := hexit y hy
    let H : ∃ i : ℕ, y + i • d ∉ Y := ⟨j, hout⟩
    have hle : Nat.find H ≤ j := Nat.find_min' H hout
    have hnot := Nat.find_spec H
    refine ⟨Nat.find H, by omega, Finset.mem_sdiff.mpr ⟨?_, hnot⟩⟩
    generalize hk : Nat.find H = k at *
    cases k with
    | zero => simp_all
    | succ k =>
      have hprev : y + k • d ∈ Y := by
        by_contra hn
        have := Nat.find_min' H hn
        omega
      exact Finset.mem_image.mpr ⟨y + k • d, hprev, by simp [succ_nsmul, add_assoc]⟩
  have hsub : Y ⊆ (Finset.range m ×ˢ boundary).image (fun t : ℕ × E => t.2 - t.1 • d) := by
    intro y hy
    obtain ⟨j, hj, hz⟩ := hfirst y hy
    exact Finset.mem_image.mpr ⟨(j, y + j • d),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, hz⟩, by simp⟩
  have hbound := (Finset.card_le_card hsub).trans Finset.card_image_le
  have hcard : (Y ∪ Y.image (· + d)).card = Y.card + boundary.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_sdiff : Disjoint Y boundary)]
    exact congrArg Finset.card (Finset.union_sdiff_self_eq_union (s := Y) (t := Y.image (· + d))).symm
  rw [hcard, Nat.mul_add]
  simpa using hbound

omit [Module ℝ E] in
/-- Among the differences from a large subset, one nonzero difference
occurs frequently enough to leave a large overlap with its translate. -/
private theorem popular_difference {A X : Finset E} {K R : ℕ} (hX : X ⊆ A)
    (hx : 2 ≤ X.card) (hr : A.card ≤ R * X.card)
    (hdiff : (A - A).card ≤ K * A.card) :
    ∃ d : E, d ≠ 0 ∧ A.card ≤ (2 * K * R ^ 2) * (X.filter (fun x => x + d ∈ X)).card := by
  classical
  let D := (A - A).erase 0
  let f : E × E → E := fun p => p.2 - p.1
  have hmaps : (X.offDiag : Set (E × E)).MapsTo f D := by
    intro p hp
    obtain ⟨hx₁, hx₂, hne⟩ := Finset.mem_offDiag.mp hp
    exact Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hne.symm, Finset.sub_mem_sub (hX hx₂) (hX hx₁)⟩
  obtain ⟨a, b, ha, hb, hne⟩ := Finset.one_lt_card_iff.mp hx
  have hD : D.Nonempty := ⟨f (a,b), hmaps (Finset.mem_offDiag.mpr ⟨ha,hb,hne⟩)⟩
  let count := fun d : E => (X.filter (fun x => x + d ∈ X)).card
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image D count hD
  refine ⟨d, (Finset.mem_erase.mp hd).1, ?_⟩
  have hfiber (e : E) :
      (X.offDiag.filter (fun p => f p = e)).card ≤ count e := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      obtain ⟨hp', he⟩ := Finset.mem_filter.mp hp
      obtain ⟨h₁, h₂, _⟩ := Finset.mem_offDiag.mp hp'
      exact Finset.mem_filter.mpr ⟨h₁, by simpa [← he, f, add_comm] using h₂⟩
    · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' he
      change x = x' at he
      subst x'
      have h := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp').2.symm
      change y - x = y' - x at h
      exact Prod.ext rfl (sub_left_injective h)
  have hpairs : X.offDiag.card ≤ (K * A.card) * count d := calc
    _ = _ := Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _ ∈ D, count d := Finset.sum_le_sum (fun e he => (hfiber e).trans (hmax e he))
    _ = D.card * count d := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ ((Finset.card_le_card (Finset.erase_subset ..)).trans hdiff)
  have hx' : X.card * 2 ≤ X.card * X.card := Nat.mul_le_mul_left _ hx
  have h₀ : X.card * X.card ≤ 2 * X.offDiag.card := by rw [Finset.offDiag_card]; omega
  have hp : 0 < A.card := lt_of_lt_of_le (by omega : 0 < X.card) (Finset.card_le_card hX)
  apply Nat.le_of_mul_le_mul_left (a := A.card) _ hp
  change A.card * A.card ≤ A.card * (2 * K * R ^ 2 * count d)
  calc
    _ ≤ (R * X.card) * (R * X.card) := Nat.mul_le_mul hr hr
    _ = R ^ 2 * (X.card * X.card) := by ring
    _ ≤ R ^ 2 * (2 * ((K * A.card) * count d)) :=
      Nat.mul_le_mul_left _ (h₀.trans (Nat.mul_le_mul_left 2 hpairs))
    _ = _ := by ring

private theorem grow_translates (K m : ℕ) (hm : 4 * K < m) (j : ℕ) :
    ∃ R N : ℕ, ∀ A : Finset E, N ≤ A.card →
      NoFiveCollinear (A : Set E) → (A - A).card ≤ K * A.card →
      (A + A + A).card ≤ K * A.card →
      ∃ X Y : Finset E, X ⊆ A ∧ A ⊆ Y ∧ A.card ≤ R * X.card ∧
        (∀ x ∈ X, ∀ y ∈ Y, x + y ∈ A + A) ∧ (m + j) * A.card ≤ m * Y.card := by
  classical
  induction j with
  | zero =>
    refine ⟨1, 1, fun A _ _ _ _ => ⟨A, A, by rfl, by rfl, by simp, ?_, by simp⟩⟩
    exact fun _ hx _ hy => Finset.add_mem_add hx hy
  | succ j ih =>
    obtain ⟨R, N, ih⟩ := ih
    refine ⟨2 * K * R ^ 2, max N (2 * R + 1), ?_⟩
    intro A hn hA hdiff htriple
    obtain ⟨X, Y, hX, hY, hsize, hsum, hgrowth⟩ :=
      ih A ((le_max_left ..).trans hn) hA hdiff htriple
    have hlarge := (le_max_right N (2 * R + 1)).trans hn
    have hx : 2 ≤ X.card := by
      by_contra! h
      have := Nat.mul_le_mul_left R (show X.card ≤ 1 by omega)
      omega
    obtain ⟨d, hd, hpop⟩ := popular_difference hX hx hsize hdiff
    let X' := X.filter (fun x => x + d ∈ X)
    let Y' := Y ∪ Y.image (· + d)
    have hg' : ∀ x ∈ X', ∀ y ∈ Y', x + y ∈ A + A := by
      intro x hmem y hy
      obtain ⟨hx₁, hx₂⟩ := Finset.mem_filter.mp hmem
      rcases Finset.mem_union.mp hy with hy | hy
      · exact hsum x hx₁ y hy
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        simpa [add_assoc, add_comm, add_left_comm] using hsum (x+d) hx₂ z hz
    refine ⟨X', Y', (Finset.filter_subset ..).trans hX, hY.trans Finset.subset_union_left,
      hpop, hg', ?_⟩
    obtain ⟨x, hxmem⟩ := Finset.card_pos.mp (show 0 < X.card by omega)
    have hexit : ∀ y ∈ Y, ∃ i < m, y + i • d ∉ Y := by
      intro y _hy
      by_contra! hall
      have hpack := progression_packing hA hd (p := x + y) (m := m) (fun i hi => by
        simpa [add_assoc] using hsum x hxmem (y + i • d) (hall i hi))
      have hl := hpack.trans (Nat.mul_le_mul_right 4 htriple)
      have hp : 0 < A.card := by omega
      have hf := Nat.mul_lt_mul_of_pos_left hm hp
      nlinarith only [hl, hf]
    have hstep := translate_growth hexit
    change (m+j+1) * A.card ≤ m * Y'.card
    calc
      _ = (m+j) * A.card + A.card := by ring
      _ ≤ m * Y.card + Y.card := Nat.add_le_add hgrowth (Finset.card_le_card hY)
      _ ≤ _ := hstep

/-- Bounded differences and bounded triple sums force five collinear points
once the cardinality exceeds a bound depending only on the two growth ratios. -/
theorem unbounded_additive_growth (K : ℕ) :
    ∃ N : ℕ, ∀ A : Finset E, N ≤ A.card → NoFiveCollinear (A : Set E) →
      (A - A).card ≤ K * A.card → K * A.card < (A + A + A).card := by
  classical
  let m := 4 * K + 1
  obtain ⟨R, N, h⟩ := grow_translates (E := E) K m (by dsimp [m]; omega) (m*K+1)
  refine ⟨max 1 N, ?_⟩
  intro A hn hcap hdiff
  by_contra! htriple
  have hp : 0 < A.card := (le_max_left 1 N).trans hn
  obtain ⟨X, Y, _, _, hx, hxy, hlarge⟩ := h A ((le_max_right ..).trans hn) hcap hdiff htriple
  have hxpos : X.Nonempty := by
    apply Finset.card_pos.mp
    by_contra! hzero
    rw [show X.card = 0 by omega, Nat.mul_zero] at hx
    omega
  obtain ⟨x, hx⟩ := hxpos
  have hY : Y.card ≤ (A + A).card :=
    Finset.card_le_card_of_injOn (x + ·) (hxy x hx) (add_right_injective x).injOn
  have h₂ : (A + A).card ≤ (A + A + A).card :=
    Finset.card_le_card_add_right (Finset.card_pos.mp hp)
  have hub := Nat.mul_le_mul_left m (hY.trans (h₂.trans htriple))
  have hstrict := Nat.mul_lt_mul_of_pos_right (show m * K < m + (m*K+1) by omega) hp
  nlinarith only [hlarge, hub, hstrict]

/-- The difference set has superlinear size, uniformly among all configurations
with at most four points on each line. -/
theorem unbounded_difference_growth (K : ℕ) :
    ∃ N : ℕ, ∀ A : Finset E, N ≤ A.card → NoFiveCollinear (A : Set E) →
      K * A.card < (A - A).card := by
  classical
  obtain ⟨N, h⟩ := unbounded_additive_growth (E := E) (K + K ^ 3)
  refine ⟨max 1 N, ?_⟩
  intro A hn hcap
  by_contra! hsmall
  have hp : 0 < A.card := (le_max_left 1 N).trans hn
  have hratio : ((A - A).card : ℚ≥0) / A.card ≤ K :=
    (div_le_iff₀ (show (0 : ℚ≥0) < A.card by exact_mod_cast hp)).mpr (by exact_mod_cast hsmall)
  have hpl := Finset.pluennecke_ruzsa_inequality_nsmul_sub (Finset.card_pos.mp hp) A 3
  have hq : (((3 : ℕ) • A).card : ℚ≥0) ≤ (K : ℚ≥0) ^ 3 * A.card :=
    hpl.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hratio 3) (by positivity))
  have hnat : ((3 : ℕ) • A).card ≤ K ^ 3 * A.card := by exact_mod_cast hq
  rw [show (3 : ℕ) = 2 + 1 by decide, succ_nsmul, two_nsmul] at hnat
  have hlow := h A ((le_max_right ..).trans hn) hcap
    (hsmall.trans (Nat.mul_le_mul_right _ (Nat.le_add_right K (K^3))))
  exact (not_lt_of_ge (hnat.trans (Nat.mul_le_mul_right _ (Nat.le_add_left (K^3) K)))) hlow


end VectorSpace
end Erdos101.DivisionRatios

open scoped Pointwise Classical

namespace Erdos101.Popular

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

private def representations (S : Finset G) (d : G) : Finset (G × G) :=
  (S ×ˢ S).filter (fun p => p.1 - p.2 = d)

/-- Each ordered pair has just one difference, so differences with multiplicity
at least `m` account for at most `|S|²` pairs in total. -/
private theorem count_differences (S D : Finset G) (m : ℝ)
    (hm : ∀ d ∈ D, m ≤ ((representations S d).card : ℝ)) :
    (D.card : ℝ) * m ≤ (S.card : ℝ) ^ 2 := by
  calc
    (D.card : ℝ) * m = ∑ _d ∈ D, m := by simp
    _ ≤ ∑ d ∈ D, ((representations S d).card : ℝ) := Finset.sum_le_sum hm
    _ ≤ (S.card : ℝ) ^ 2 := by
      have h := Finset.sum_card_fiberwise_eq_card_filter (S ×ˢ S) D
        (fun p : G × G => p.1 - p.2)
      have h' := h.le.trans (Finset.card_filter_le ..)
      simp only [Finset.card_product, ← sq] at h'
      exact_mod_cast h'

/-- If every vertex in `V` has few low-codegree partners in `U`, then the
differences of `V` have many representations by pairs of popular differences of `C`. -/
theorem difference_bound (B C U V : Finset G) (τ : ℝ) (hτ : 0 < τ)
    (hgood : ∀ x ∈ V, ((U.filter (fun z =>
      ((B.filter (fun b => x + b ∈ C ∧ z + b ∈ C)).card : ℝ) < τ)).card : ℝ) ≤ (U.card : ℝ) / 4) :
    ((V - V).card : ℝ) * (U.card : ℝ) / 2 ≤ (((C.card : ℝ) ^ 2) / τ) ^ 2 := by
  let P := (C - C).filter (fun d => τ ≤ ((representations C d).card : ℝ))
  have hP : (P.card : ℝ) ≤ (C.card : ℝ) ^ 2 / τ :=
    (le_div_iff₀ hτ).mpr (count_differences C P τ (fun _ hd => (Finset.mem_filter.mp hd).2))
  let common (x z : G) := B.filter (fun b => x + b ∈ C ∧ z + b ∈ C)
  let bad (x : G) := U.filter (fun z => ((common x z).card : ℝ) < τ)
  -- Each common neighbor b gives the pair (x + b,z + b) of difference x - z.
  have popular (x z : G) (hz : z ∈ U) (h : z ∉ bad x) : x - z ∈ P := by
    have hn : τ ≤ ((common x z).card : ℝ) :=
      le_of_not_gt (fun hlt => h (Finset.mem_filter.mpr ⟨hz, hlt⟩))
    have hmap : (common x z).card ≤ (representations C (x - z)).card := by
      apply Finset.card_le_card_of_injOn (fun b => (x + b, z + b))
      · intro b hb
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr (Finset.mem_filter.mp hb).2, by simp⟩
      · intro b _ c _ hbc
        exact add_left_cancel (congrArg Prod.fst hbc)
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (common x z).card by exact_mod_cast hτ.trans_le hn)
    obtain ⟨hb₁, hb₂⟩ := (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨by simpa using Finset.sub_mem_sub hb₁ hb₂, hn.trans (by exact_mod_cast hmap)⟩
  have hmult (d : G) (hd : d ∈ V - V) : (U.card : ℝ) / 2 ≤ ((representations P d).card : ℝ) := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hd
    let W := U \ (bad x ∪ bad y)
    have hcover : U.card ≤ W.card + ((bad x).card + (bad y).card) :=
      Finset.card_le_card_sdiff_add_card.trans (Nat.add_le_add_left (Finset.card_union_le ..) _)
    have hw : (U.card : ℝ) / 2 ≤ (W.card : ℝ) := by
      have hr : (U.card : ℝ) ≤ W.card + ((bad x).card + (bad y).card : ℝ) := by exact_mod_cast hcover
      have hx' : ((bad x).card : ℝ) ≤ (U.card : ℝ) / 4 := hgood x hx
      have hy' : ((bad y).card : ℝ) ≤ (U.card : ℝ) / 4 := hgood y hy
      linarith only [hr, hx', hy']
    -- Distinct z in W give distinct pairs (x - z,y - z) with the same difference x - y.
    have hinj : W.card ≤ (representations P (x - y)).card := by
      apply Finset.card_le_card_of_injOn (fun z => (x - z, y - z))
      · intro z hz
        obtain ⟨hu, hb⟩ := Finset.mem_sdiff.mp hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨popular x z hu (fun h => hb (Finset.mem_union_left _ h)),
           popular y z hu (fun h => hb (Finset.mem_union_right _ h))⟩, by simp⟩
      · intro z _ w _ h
        exact sub_right_injective (congrArg Prod.fst h)
    exact hw.trans (by exact_mod_cast hinj)
  calc
    ((V - V).card : ℝ) * (U.card : ℝ) / 2 = ((V - V).card : ℝ) * ((U.card : ℝ) / 2) := by ring
    _ ≤ (P.card : ℝ) ^ 2 := count_differences P (V - V) _ hmult
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hP 2

end Erdos101.Popular

namespace Erdos101.DivisionRatios

open scoped Classical Pointwise

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- Uniformly in three point sets of the same size, a positive fraction of
all sums cannot land in the third set when the first set has no five collinear. -/
theorem sparse_restricted_sums (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ A B C : Finset E, N ≤ A.card → B.card = A.card → C.card ≤ A.card →
      NoFiveCollinear (A : Set E) →
      (((A ×ˢ B).filter (fun p => p.1 + p.2 ∈ C)).card : ℝ) < ε * (A.card : ℝ)^2 := by
  classical
  let c := min ε 1
  have hc : 0 < c := lt_min hε zero_lt_one
  obtain ⟨K, hK⟩ := exists_nat_gt (4096 / c^6)
  obtain ⟨M, hM⟩ := unbounded_difference_growth (E := E) K
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (M : ℝ) / c)
  refine ⟨max 1 N, ?_⟩
  intro A B C hn hB hC hA
  by_contra! hdense
  have ha : 0 < A.card := (le_max_left 1 N).trans hn
  have han : 0 < (A.card : ℝ) := by exact_mod_cast ha
  let F := (A ×ˢ B).filter (fun p => p.1 + p.2 ∈ C)
  have hF : c * (A.card : ℝ) * B.card ≤ F.card := by
    rw [hB, mul_assoc, ← sq]
    exact (mul_le_mul_of_nonneg_right (min_le_left ε 1) (sq_nonneg _)).trans hdense
  obtain ⟨U, hUA, hsize, hbad⟩ := Finset.graph_pair_dependentRandomChoice A B
    (Finset.card_pos.mp ha) (Finset.card_pos.mp (hB ▸ ha))
    F (Finset.filter_subset ..) c hc (min_le_right ..) hF (1/8) (by norm_num) (by norm_num)
  have hU : 0 < (U.card : ℝ) := lt_of_lt_of_le (by positivity) hsize
  let τ := ((1/8 : ℝ) * c^2 / 2) * B.card
  have ht : τ = c^2 * A.card / 16 := by dsimp [τ]; rw [hB]; ring
  have htpos : 0 < τ := by rw [ht]; positivity
  obtain ⟨V, hVU, hhalf, hgood⟩ := Finset.graph_dependentRandomChoice_markov_refinement
    B U F τ (1/8) (by norm_num) hU (by simpa only [Finset.filter_and] using hbad)
  have hV : c * A.card / 4 ≤ (V.card : ℝ) := by linarith
  have hUhalf : c * A.card / 4 ≤ (U.card : ℝ) / 2 := by linarith
  have hMV : M ≤ V.card := by
    have hNA : (N : ℝ) ≤ A.card := by exact_mod_cast (le_max_right 1 N).trans hn
    have hMN := ((div_lt_iff₀ hc).mp hN).trans_le (mul_le_mul_of_nonneg_right hNA hc.le)
    exact_mod_cast (show (M : ℝ) ≤ V.card by linarith)
  have hlower := hM V hMV (fun T hT => hA T (hT.trans (Finset.coe_subset.mpr (hVU.trans hUA))))
  have hdiff := Erdos101.Popular.difference_bound B C U V τ htpos (by
    intro x hx
    have heq (z : E) (hz : z ∈ U) :
        B.filter (fun b => (x,b) ∈ F ∧ (z,b) ∈ F) =
          B.filter (fun b => x+b ∈ C ∧ z+b ∈ C) := by
      ext b
      simp [F, hUA (hVU hx), hUA hz, and_assoc, and_left_comm]
    have heq' := Finset.filter_congr (s := U) (fun z hz =>
      show (((B.filter (fun b => (x,b) ∈ F ∧ (z,b) ∈ F)).card : ℝ) < τ) ↔
          (((B.filter (fun b => x+b ∈ C ∧ z+b ∈ C)).card : ℝ) < τ) by rw [heq z hz])
    have h := hgood x hx
    rw [heq'] at h
    linarith)
  have hquot : (C.card : ℝ)^2 / τ ≤ 16 / c^2 * A.card := by
    apply (div_le_iff₀ htpos).mpr
    calc
      (C.card : ℝ)^2 ≤ (A.card : ℝ)^2 :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast hC) 2
      _ = 16 / c^2 * A.card * τ := by rw [ht]; field_simp
  have hfinal : ((V-V).card : ℝ) ≤ (K : ℝ) * V.card := by
    apply le_of_mul_le_mul_right _ (show 0 < (U.card : ℝ) / 2 by positivity)
    calc
      ((V-V).card : ℝ) * ((U.card : ℝ)/2) = ((V-V).card : ℝ)*U.card/2 := by ring
      _ ≤ _ := hdiff
      _ ≤ (16 / c^2 * (A.card : ℝ))^2 := pow_le_pow_left₀ (by positivity) hquot 2
      _ = 4096 / c^6 * (c * A.card / 4) * (c * A.card / 4) := by field_simp; ring
      _ ≤ (K : ℝ) * V.card * ((U.card : ℝ)/2) :=
        mul_le_mul (mul_le_mul hK.le hV (by positivity) (by positivity)) hUhalf
          (by positivity) (by positivity)
  exact (not_lt_of_ge (show (V-V).card ≤ K * V.card by exact_mod_cast hfinal)) hlower

end Erdos101.DivisionRatios

noncomputable section

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

/-- The three arbitrary height functions may all depend on the full configuration. -/
theorem sparse_homogeneous_sums (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ S : Finset ℝ², N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
      ∀ f g h : Height,
        (((S ×ˢ S).filter (fun p => lift f p.1 + lift g p.2 ∈ S.image (lift h))).card : ℝ)
          < ε * (S.card : ℝ)^2 := by
  classical
  obtain ⟨N,hN⟩ := DivisionRatios.sparse_restricted_sums (E := ℝ × ℝ²) ε hε
  refine ⟨N,?_⟩
  intro S hn hS f g h
  have hsize (k : Height) : (S.image (lift k)).card = S.card :=
    Finset.card_image_of_injective _ (lift_injective k)
  have hb := hN (S.image (lift f)) (S.image (lift g)) (S.image (lift h))
    (by simpa only [hsize] using hn) (by simp only [hsize]) (by simp only [hsize, le_refl])
    (lift_no_five hS f)
  rw [hsize] at hb
  apply lt_of_le_of_lt _ hb
  apply Nat.cast_le.mpr
  apply Finset.card_le_card_of_injOn (fun p : ℝ² × ℝ² => (lift f p.1, lift g p.2))
  · intro p hp
    obtain ⟨hp,hs⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hx,Finset.mem_image_of_mem _ hy⟩,hs⟩
  · intro p _ q _ he
    exact Prod.ext (lift_injective f (congrArg Prod.fst he)) (lift_injective g (congrArg Prod.snd he))

end Erdos101.ProjectiveSums

end

/-
# Triangle ratios of a family of selected collinear triples

The three pairs in a triangle can come from three different selected triples.
Two applications of graph triangle removal give a dense family of the original
triples whose weights are determined, up to the observed triangle ratios, by
two fixed vertices.
-/

noncomputable section

namespace Erdos101.Ceva

open SimpleGraph TripartiteFromTriangles
open scoped Classical

section Triples

variable {α : Type*} [Fintype α] [DecidableEq α]

def XY (T : Finset (α × α × α)) (x y : α) : Prop := ∃ z, (x,y,z) ∈ T
def XZ (T : Finset (α × α × α)) (x z : α) : Prop := ∃ y, (x,y,z) ∈ T
def YZ (T : Finset (α × α × α)) (y z : α) : Prop := ∃ x, (x,y,z) ∈ T

def atLast (T : Finset (α × α × α)) (p : α) :=
  T.filter (fun e => XZ T e.1 p ∧ YZ T e.2.1 p)

def anchorDensity (δ : ℝ) := triangleRemovalBound (δ/9)

theorem anchorDensity_pos {δ : ℝ} (hδ : 0 < δ) : 0 < anchorDensity δ :=
  triangleRemovalBound_pos (div_pos hδ (by norm_num))

/-- One vertex in the last class sees both endpoints of a positive density
of the original records. The triangles counted by removal may be mixed. -/
theorem anchor_last [Nonempty α] (T : Finset (α × α × α)) [ExplicitDisjoint T]
    {δ : ℝ} (hδ : 0 < δ) (hT : δ * (Fintype.card α : ℝ)^2 ≤ T.card) :
    ∃ p, anchorDensity δ * (Fintype.card α : ℝ)^2 ≤ (atLast T p).card := by
  classical
  have hfar : (graph T).FarFromTriangleFree (δ/9) := by
    apply farFromTriangleFree
    push_cast
    calc
      _ = δ * (Fintype.card α : ℝ)^2 := by ring
      _ ≤ _ := hT
  let C := (graph T).cliqueFinset 3
  let image (p : α) := (atLast T p).image (fun e => toTriangle (e.1,e.2.1,p))
  have hsub : C ⊆ Finset.univ.biUnion image := by
    intro s hs
    have hs' : (graph T).IsNClique 3 s := SimpleGraph.mem_cliqueFinset_iff.mp hs
    obtain ⟨i,j,k,hij,hik,hjk,rfl⟩ := SimpleGraph.is3Clique_iff.mp hs'
    obtain ⟨x,y,p,he,hxy,hxp,hyp⟩ := graph_triple hij hik hjk
    obtain ⟨z,ht⟩ := Graph.in₀₁_iff.mp hxy
    exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_univ _,Finset.mem_image.mpr
      ⟨(x,y,z), Finset.mem_filter.mpr ⟨ht, Graph.in₀₂_iff.mp hxp, Graph.in₁₂_iff.mp hyp⟩,he⟩⟩
  obtain ⟨p,_,hbig⟩ := Finset.exists_max_image (Finset.univ : Finset α)
    (fun a => (atLast T a).card) Finset.univ_nonempty
  have hC : C.card ≤ Fintype.card α * (atLast T p).card := calc
    _ ≤ _ := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _ : α, (atLast T p).card := Finset.sum_le_sum
      (fun a ha => Finset.card_image_le.trans (hbig a ha))
    _ = _ := by simp
  have hlarge : anchorDensity δ * (Fintype.card α : ℝ)^3 ≤ C.card := by
    apply le_trans _ hfar.le_card_cliqueFinset
    dsimp [anchorDensity]
    gcongr
    simp only [Fintype.card_sum]
    omega
  have hn : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr (Fintype.card_pos (α := α))
  refine ⟨p,le_of_mul_le_mul_right ?_ hn⟩
  calc
    _ = anchorDensity δ * (Fintype.card α : ℝ)^3 := by ring
    _ ≤ C.card := hlarge
    _ ≤ _ := by
      rw [mul_comm]
      exact_mod_cast hC

private def swapLast : (α × α × α) ↪ (α × α × α) :=
  ⟨fun e => (e.1,e.2.2,e.2.1), by rintro ⟨a,b,c⟩ ⟨d,e,f⟩ h; simpa [and_comm] using h⟩

omit [Fintype α] [DecidableEq α] in
private theorem mem_swap {T : Finset (α × α × α)} {x y z : α} :
    (x,y,z) ∈ T.map swapLast ↔ (x,z,y) ∈ T := by
  constructor
  · intro h
    obtain ⟨⟨a,b,c⟩,he,hh⟩ := Finset.mem_map.mp h
    change (a,c,b) = (x,y,z) at hh
    obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj hh |>.imp_right Prod.mk.inj
    exact he
  · exact fun h => Finset.mem_map.mpr ⟨(x,z,y),h,rfl⟩

omit [Fintype α] [DecidableEq α] in
private theorem disjoint_subset {T U : Finset (α × α × α)} (hd : ExplicitDisjoint T) (hU : U ⊆ T) :
    ExplicitDisjoint U :=
  ⟨fun {_ _ _ _} he hf => hd.inj₀ (hU he) (hU hf),fun {_ _ _ _} he hf => hd.inj₁ (hU he) (hU hf),
   fun {_ _ _ _} he hf => hd.inj₂ (hU he) (hU hf)⟩

omit [Fintype α] [DecidableEq α] in
private theorem disjoint_swap {T : Finset (α × α × α)} (h : ExplicitDisjoint T) :
    ExplicitDisjoint (T.map swapLast) :=
  ⟨fun {_ _ _ _} he hf => h.inj₀ (mem_swap.mp he) (mem_swap.mp hf),
   fun {_ _ _ _} he hf => h.inj₂ (mem_swap.mp he) (mem_swap.mp hf),
   fun {_ _ _ _} he hf => h.inj₁ (mem_swap.mp he) (mem_swap.mp hf)⟩

/-- Two fixed vertices suffice to test the three mixed triangles used in the
weight comparison. Each selected triple retains its original three entries. -/
theorem two_anchors [Nonempty α] (T : Finset (α × α × α)) [hd : ExplicitDisjoint T]
    {δ : ℝ} (hδ : 0 < δ) (hT : δ * (Fintype.card α : ℝ)^2 ≤ T.card) :
    ∃ (p q : α) (U : Finset (α × α × α)), U ⊆ T ∧
      anchorDensity (anchorDensity δ) * (Fintype.card α : ℝ)^2 ≤ U.card ∧
      YZ T q p ∧ ∀ e ∈ U, XZ T e.1 p ∧ YZ T e.2.1 p ∧ XY T e.1 q ∧ YZ T q e.2.2 := by
  classical
  obtain ⟨p,hp⟩ := anchor_last T hδ hT
  let P := atLast T p
  have hP : P ⊆ T := Finset.filter_subset .. 
  let T' := P.map swapLast
  have : ExplicitDisjoint T' := disjoint_swap (disjoint_subset hd hP)
  obtain ⟨q,hq⟩ := anchor_last T' (anchorDensity_pos hδ)
    (by simpa only [T',Finset.card_map] using hp)
  let U := (atLast T' q).map swapLast
  have hsize : anchorDensity (anchorDensity δ) * (Fintype.card α : ℝ)^2 ≤ U.card := by
    simpa only [U,Finset.card_map] using hq
  have info {x y z : α} (he : (x,y,z) ∈ U) :
      (x,y,z) ∈ T ∧ XZ T x p ∧ YZ T y p ∧ XY T x q ∧ YZ T q z := by
    obtain ⟨he',⟨b,hb⟩,⟨a,ha⟩⟩ := Finset.mem_filter.mp (mem_swap.mp he)
    have hp' := mem_swap.mp he'
    obtain ⟨h₁,h₂,h₃⟩ := Finset.mem_filter.mp hp'
    exact ⟨h₁,h₂,h₃,⟨b,hP (mem_swap.mp hb)⟩,⟨a,hP (mem_swap.mp ha)⟩⟩
  have hpos : (0 : ℝ) < U.card := lt_of_lt_of_le
    (mul_pos (anchorDensity_pos (anchorDensity_pos hδ)) (by positivity)) hsize
  obtain ⟨⟨x,y,z⟩,he⟩ := Finset.card_pos.mp (Nat.cast_pos.mp hpos)
  obtain ⟨_,⟨b,hb⟩,_⟩ := Finset.mem_filter.mp (mem_swap.mp he)
  have hqp := (Finset.mem_filter.mp (mem_swap.mp hb)).2.2
  exact ⟨p,q,U,fun _ he => (info he).1,hsize,hqp,fun _ he => (info he).2⟩

end Triples

open EuclideanGeometry ProjectiveSums

/-- The two coefficients give the affine expression for the third point.
The third table records their ratio on the pair of first and second points. -/
def Represents (S : Finset ℝ²) (T : Finset (S × S × S)) (a b d : S → S → ℝˣ) : Prop :=
  ∀ e ∈ T, (a e.1 e.2.2 : ℝ) + (b e.2.1 e.2.2 : ℝ) = 1 ∧
    (a e.1 e.2.2 : ℝ) • (e.1 : ℝ²) + (b e.2.1 e.2.2 : ℝ) • (e.2.1 : ℝ²) = (e.2.2 : ℝ²) ∧
    d e.1 e.2.1 = b e.2.1 e.2.2 / a e.1 e.2.2

/-- The signed product around a triangle in the graph of observed pairs.
The three supporting records may be different. -/
def triangleRatio {α : Type*} (a b d : α → α → ℝˣ) (x y z : α) : ℝˣ :=
  a x z * d x y / b y z

private def extendHeight (S : Finset ℝ²) (f : S → ℝˣ) : Height :=
  fun x => if hx : x ∈ S then f ⟨x,hx⟩ else 1

private theorem lift_of_coefficients {S : Finset ℝ²} (f g h : S → ℝˣ) {x y z : S}
    {a b : ℝˣ} (hs : (a : ℝ) + b = 1) (hv : (a : ℝ) • (x : ℝ²) + (b : ℝ) • (y : ℝ²) = z)
    (hf : f x = h z*a) (hg : g y = h z*b) :
    lift (extendHeight S f) x + lift (extendHeight S g) y = lift (extendHeight S h) z := by
  apply Prod.ext
  · change ((extendHeight S f x : ℝ) + (extendHeight S g y : ℝ)) = (extendHeight S h z : ℝ)
    simp only [extendHeight,dif_pos x.property,dif_pos y.property,dif_pos z.property,hf,hg,Units.val_mul]
    rw [← mul_add,hs,mul_one]
  · change (extendHeight S f x : ℝ) • (x : ℝ²) + (extendHeight S g y : ℝ) • (y : ℝ²) =
      (extendHeight S h z : ℝ) • (z : ℝ²)
    simp only [extendHeight,dif_pos x.property,dif_pos y.property,dif_pos z.property,hf,hg,Units.val_mul]
    rw [← smul_smul,← smul_smul,← smul_add,hv]

/-- If the triangle ratios of a linear family of collinear triples take at most
`k` distinct values, the family has uniformly subquadratic size. -/
theorem sparse_bounded_triangle_ratios (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ S : Finset ℝ², N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
    ∀ (T : Finset (S × S × S)), ExplicitDisjoint T → ∀ (a b d : S → S → ℝˣ), Represents S T a b d →
    ∀ (K : Finset ℝˣ), K.card ≤ k →
      (∀ x y z, XY T x y → XZ T x z → YZ T y z → triangleRatio a b d x y z ∈ K) →
      (T.card : ℝ) < δ*(S.card : ℝ)^2 := by
  classical
  let c := anchorDensity (anchorDensity δ)
  have hc : 0 < c := anchorDensity_pos (anchorDensity_pos hδ)
  let η := c / ((k : ℝ)+1)^3
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N,hN⟩ := sparse_homogeneous_sums η hη
  refine ⟨max N 1,?_⟩
  intro S hn hcap T hd a b d hw K hk hK
  by_contra! hdense
  have hns : 0 < S.card := (le_max_right N 1).trans hn
  have hnr : (0 : ℝ) < S.card := Nat.cast_pos.mpr hns
  have : Nonempty S := Finset.nonempty_coe_sort.mpr (Finset.card_pos.mp hns)
  obtain ⟨p,q,U,hUT,hsize,hqp,hpairs⟩ := two_anchors T hδ (by simpa using hdense)
  let ratio := triangleRatio a b d
  let color (e : S × S × S) := (ratio e.1 e.2.1 p, ratio e.1 q p, ratio e.1 q e.2.2)
  let W := K ×ˢ (K ×ˢ K)
  have hmap : Set.MapsTo color (U : Set _) (W : Set _) := by
    rintro ⟨x,y,z⟩ he
    obtain ⟨hxp,hyp,hxq,hqz⟩ := hpairs _ he
    have hT := hUT he
    exact Finset.mem_product.mpr ⟨hK _ _ _ ⟨z,hT⟩ hxp hyp,Finset.mem_product.mpr
      ⟨hK _ _ _ hxq hxp hqp,hK _ _ _ hxq ⟨y,hT⟩ hqz⟩⟩
  let fiber (w : ℝˣ × ℝˣ × ℝˣ) := U.filter (fun e => color e = w)
  have bound (w : ℝˣ × ℝˣ × ℝˣ) : ((fiber w).card : ℝ) < η*(S.card : ℝ)^2 := by
    let f (x : S) := a x p * w.2.2 / w.2.1
    let g (y : S) := b y p * w.1 * w.2.2 / w.2.1
    let h (z : S) := b q p / b q z
    have hs := hN S ((le_max_left ..).trans hn) hcap (extendHeight S f) (extendHeight S g) (extendHeight S h)
    apply lt_of_le_of_lt _ hs
    apply Nat.cast_le.mpr
    apply Finset.card_le_card_of_injOn (fun e : S × S × S => ((e.1 : ℝ²),(e.2.1 : ℝ²)))
    · rintro ⟨x,y,z⟩ he
      obtain ⟨hu,heq⟩ := Finset.mem_filter.mp he
      obtain ⟨hsum,hvec,hdxy⟩ := hw _ (hUT hu)
      obtain rfl : w = (ratio x y p,ratio x q p,ratio x q z) := heq.symm
      have hf : f x = h z*a x z := by
        apply Units.ext
        simp [f,h,ratio,triangleRatio]
        field_simp
      have hg : g y = h z*b y z := by
        apply Units.ext
        simp [g,h,ratio,triangleRatio,hdxy]
        field_simp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨x.property,y.property⟩,
        Finset.mem_image.mpr ⟨z,z.property,(lift_of_coefficients f g h hsum hvec hf hg).symm⟩⟩
    · rintro ⟨x,y,z⟩ he ⟨x',y',z'⟩ he' hxy
      obtain rfl : x = x' := Subtype.ext (congrArg Prod.fst hxy)
      obtain rfl : y = y' := Subtype.ext (congrArg Prod.snd hxy)
      have hzz := hd.inj₂ (hUT (Finset.mem_filter.mp he).1) (hUT (Finset.mem_filter.mp he').1)
      simpa using hzz
  have hmass : (U.card : ℝ) ≤ W.card*(η*(S.card : ℝ)^2) := calc
    _ = ∑ w ∈ W, ((fiber w).card : ℝ) := by exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _w ∈ W, η*(S.card : ℝ)^2 := Finset.sum_le_sum (fun w _ => (bound w).le)
    _ = _ := by simp
  have hcard : W.card ≤ k^3 := by
    simp only [W,Finset.card_product]
    calc
      _ ≤ k*(k*k) := Nat.mul_le_mul hk (Nat.mul_le_mul hk hk)
      _ = _ := by ring
  have hstrict : (W.card : ℝ) < ((k : ℝ)+1)^3 :=
    (show (W.card : ℝ) ≤ (k : ℝ)^3 by exact_mod_cast hcard).trans_lt (by gcongr; linarith)
  have hupper : (U.card : ℝ) < c*(S.card : ℝ)^2 := calc
    _ ≤ _ := hmass
    _ < ((k : ℝ)+1)^3 * (η*(S.card : ℝ)^2) := mul_lt_mul_of_pos_right hstrict (by positivity)
    _ = _ := by dsimp [η]; field_simp
  exact (not_lt_of_ge (by simpa [c] using hsize)) hupper

end Erdos101.Ceva

end

theorem OMA.solution : OMA.R_Erdos101_erdos_101_R2.H2 :=
  Erdos101.Ceva.sparse_bounded_triangle_ratios
