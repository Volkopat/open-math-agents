import OMAReductions.R_Erdos101_erdos_101_R2
import Mathlib

-- Proof of the bounded triangle-ratio step for Erdős 101.
-- Credit: @ubuwaits

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


/-!
# Graph Balog–Szemerédi–Gowers theorem

The eleven lemma declarations below are selected from Adam McKenna’s
LeanFormalizations.Combinatorics.Additive.BalogSzemerediGowers at commit
db02244c25aecd74eb96d9186c922387824c1258. The other declarations have been
omitted. The original license text follows the proof.

https://github.com/mysticflounder/lean-formalizations/blob/db02244c25aecd74eb96d9186c922387824c1258/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean
-/

namespace Finset

open scoped Pointwise

/--
**Length-3 path count is dominated by a triple-rep count in `S × S × S`.**

For a bipartite graph `E ⊆ A ×ˢ B` over an additive commutative group, fix a
restricted sumset `S` containing all sums `p.1 + p.2` for `p ∈ E`. For any
`a, b ∈ G`, the number of length-3 paths `a — b₁ — a₁ — b` in `E` is at most
the number of triples `(s₁, s₂, s₃) ∈ S × S × S` with `s₁ - s₂ + s₃ = a + b`.

Proof: the map `(b₁, a₁) ↦ (a + b₁, a₁ + b₁, a₁ + b)` sends each path to a
triple in `S × S × S` (because each edge `(x, y) ∈ E` has `x + y ∈ S`) summing
to `a + b` under `s₁ - s₂ + s₃`. It is injective: `b₁` is recovered from
`(a + b₁) - a` (or equivalently from the first coordinate minus the constant `a`),
and `a₁` is recovered from the third coordinate as `(a₁ + b) - b`.

Used by `graph_balogSzemerediGowers_restricted_sumset` to bridge the pointwise
length-3 path count (supplied by `dense_bipartite_has_path3_rectangle` via
dependent random choice) to the triple-rep multiplicity hypothesis of
`restricted_sumset_via_multiplicity`. Tao-Vu, *Additive Combinatorics*, §6.4
(Cor. 6.20).
-/
lemma path3_count_le_triple_rep_count {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B S : Finset G) (E : Finset (G × G)) (hSdef : ∀ p ∈ E, p.1 + p.2 ∈ S)
    (a b : G) :
    (((B ×ˢ A).filter fun q : G × G ↦
        (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ)
    ≤ ((S ×ˢ S ×ˢ S).filter
        fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card := by
  -- Define the map (b₁, a₁) ↦ (a + b₁, a₁ + b₁, a₁ + b).
  set f : G × G → G × G × G := fun q ↦ (a + q.1, q.2 + q.1, q.2 + b) with hf_def
  set src : Finset (G × G) :=
    (B ×ˢ A).filter (fun q : G × G ↦
      (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E) with hsrc_def
  set tgt : Finset (G × G × G) :=
    (S ×ˢ S ×ˢ S).filter (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)
    with htgt_def
  apply Finset.card_le_card_of_injOn f
  · -- MapsTo: f sends src into tgt.
    intro q hq
    simp only [hsrc_def, Finset.coe_filter, Set.mem_ofPred_eq,
      Finset.mem_product] at hq
    obtain ⟨⟨_hq1B, _hq2A⟩, hEab1, hEa1b1, hEa1b⟩ := hq
    have hs1 : a + q.1 ∈ S := hSdef (a, q.1) hEab1
    have hs2 : q.2 + q.1 ∈ S := hSdef (q.2, q.1) hEa1b1
    have hs3 : q.2 + b ∈ S := hSdef (q.2, b) hEa1b
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, ?_⟩)
    · exact Finset.mem_product.mpr ⟨hs1, Finset.mem_product.mpr ⟨hs2, hs3⟩⟩
    · -- (a + b₁) - (a₁ + b₁) + (a₁ + b) = a + b.
      show (a + q.1) - (q.2 + q.1) + (q.2 + b) = a + b
      abel
  · -- InjOn: f is injective on src.
    intro q₁ _hq₁ q₂ _hq₂ hfeq
    -- f q₁ = f q₂ means (a + q₁.1, q₁.2 + q₁.1, q₁.2 + b) = (a + q₂.1, …, q₂.2 + b).
    -- Project out the first and third coordinates of the triple equality.
    have h1 : a + q₁.1 = a + q₂.1 := by
      have := congrArg Prod.fst hfeq
      simpa [hf_def] using this
    have h3 : q₁.2 + b = q₂.2 + b := by
      have := congrArg (fun p : G × G × G ↦ p.2.2) hfeq
      simpa [hf_def] using this
    have hq1eq : q₁.1 = q₂.1 := add_left_cancel h1
    have hq2eq : q₁.2 = q₂.2 := add_right_cancel h3
    exact Prod.ext hq1eq hq2eq

/--
**Restricted sumset upper bound via difference-set multiplicity.**

Let `A, B, S ⊆ G`. If every `(a, b) ∈ A × B` admits at least `M` triples
`(s₁, s₂, s₃) ∈ S × S × S` with `s₁ - s₂ + s₃ = a + b`, then
`M · |A + B| ≤ |S|³`.

Proof: the disjoint fibers `T_v := { (s₁, s₂, s₃) ∈ S × S × S : s₁ - s₂ + s₃ = v }`
indexed by `v ∈ A + B` each contain ≥ M triples and embed into `S × S × S`,
so `M · |A + B| ≤ ∑_{v ∈ A + B} |T_v| ≤ |S|³`.

This is the standard sumset bound used in the Tao-Vu / Petridis path-counting
proof of Balog-Szemerédi-Gowers: the triple-counting step inside the proof of
Tao-Vu, *Additive Combinatorics*, Theorem 2.29 (§6.4) — `#triples ≤ |A+B|³` —
not a separately numbered lemma.
-/
lemma restricted_sumset_via_multiplicity {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B S : Finset G) (M : ℕ) :
    (∀ a ∈ A, ∀ b ∈ B,
        M ≤ ((S ×ˢ S ×ˢ S).filter
          (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)).card) →
    M * (A + B).card ≤ S.card ^ 3 := by
  intro hcover
  -- Build the disjoint sets T_v = { (s₁,s₂,s₃) ∈ S × S × S : s₁ - s₂ + s₃ = v }.
  set T : G → Finset (G × G × G) :=
    fun v ↦ (S ×ˢ S ×ˢ S).filter (fun p ↦ p.1 - p.2.1 + p.2.2 = v) with hT_def
  -- Each fiber T_v contributes at least M to the sum over A + B.
  have hMle : ∀ v ∈ A + B, M ≤ (T v).card := by
    intro v hv
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hv
    -- Substitute a + b = v in the multiplicity hypothesis.
    have hM_at := hcover a ha b hb
    -- The triple subset T(a,b) has card ≥ M, and lies inside T v.
    set T_ab : Finset (G × G × G) :=
      (S ×ˢ S ×ˢ S).filter
        (fun p ↦ p.1 - p.2.1 + p.2.2 = a + b) with hTab_def
    have hT_ab_eq : T_ab = T v := by
      apply Finset.filter_congr
      intro p _
      constructor
      · intro h; rw [h, hab]
      · intro h; rw [h, ← hab]
    have : M ≤ T_ab.card := hM_at
    rw [hT_ab_eq] at this
    exact this
  -- The fibers cover disjointly inside S × S × S.
  -- Sum over v ∈ A + B of |T_v| ≤ |S × S × S| = |S|^3.
  have hdisj : ((A + B : Finset G) : Set G).PairwiseDisjoint T := by
    intro v _ w _ hvw
    refine Finset.disjoint_filter.mpr ?_
    intro p _ hpv hpw
    exact hvw (hpv ▸ hpw)
  have hSubset : ∀ v ∈ A + B, T v ⊆ S ×ˢ S ×ˢ S := by
    intro v _ p hp
    exact (Finset.mem_filter.mp hp).1
  -- Σ_v |T_v| = | ⋃_v T_v | ≤ |S × S × S|.
  have hSumCard :
      ∑ v ∈ A + B, (T v).card = ((A + B).biUnion T).card := by
    rw [Finset.card_biUnion]
    intro v hv w hw hvw
    have hpw : ((A + B : Finset G) : Set G).PairwiseDisjoint T := hdisj
    have hv' : v ∈ ((A + B : Finset G) : Set G) := hv
    have hw' : w ∈ ((A + B : Finset G) : Set G) := hw
    exact hpw hv' hw' hvw
  have hSumLeS3 : ∑ v ∈ A + B, (T v).card ≤ (S ×ˢ S ×ˢ S).card := by
    rw [hSumCard]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨v, hv, hpv⟩ := hp
    exact hSubset v hv hpv
  -- Σ_v M ≤ Σ_v |T_v|.
  have hML : M * (A + B).card ≤ ∑ v ∈ A + B, (T v).card := by
    have hsum_le : ∑ _v ∈ A + B, M ≤ ∑ v ∈ A + B, (T v).card :=
      Finset.sum_le_sum (fun v hv ↦ hMle v hv)
    have hconst : ∑ _v ∈ A + B, M = (A + B).card * M := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [hconst, mul_comm] at hsum_le
    exact hsum_le
  -- Combine.
  have hCard_S3 : (S ×ˢ S ×ˢ S).card = S.card ^ 3 := by
    rw [Finset.card_product, Finset.card_product, pow_succ, pow_succ, pow_one]
    ring
  calc M * (A + B).card
      ≤ ∑ v ∈ A + B, (T v).card := hML
    _ ≤ (S ×ˢ S ×ˢ S).card := hSumLeS3
    _ = S.card ^ 3 := hCard_S3

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

/--
**Dense bipartite graph has a pointwise length-3 path rectangle (Fox-Sudakov
Lemma 5.2 / Tao-Vu Cor. 6.20).** Given a bipartite graph `E ⊆ A ×ˢ B` of density
`≥ δ` (with `|A| = |B|`), there exist subsets `A' ⊆ A`, `B' ⊆ B` of cardinality
`≥ (δ / 8) · |A|` such that *every* pair `(a, b) ∈ A' × B'` admits at least
`(δ^5 / 2^12) · |A|^2` length-3 paths `a — b₁ — a₁ — b` in `E`. The path
multiplicity is **pointwise**, not averaged — this is what makes the bound
linear when fed into the triple-rep count.

Proof: dependent random choice (as implemented). (1) Restrict to the popular
rows `A₁ := {a : deg_E(a) ≥ (δ/2)|B|}` and edges `E₁` out of them; `E₁` still
has density `≥ δ/2`. (2) Pair-DRC (Fox-Sudakov 5.1): pick a *column* vertex
`v ∈ B` uniformly and set the core `U := N_{E₁}(v) ⊆ A₁ ⊆ A`; by Cauchy-Schwarz
a positive fraction of `v` give both `|U| ≥ (δ/4)|A|` and few "bad" ordered
pairs `(a, a') ∈ U × U` of low codegree `|N(a) ∩ N(a')| < τ`. (3) `A' ⊆ U` is
the Markov refinement to vertices with `≤ (δ/8)|U|` bad partners in `U`; (4)
`B' ⊆ B` is the popular columns, those with `≥ (δ/4)|U|` neighbors inside `U`.
The high pointwise codegree on `A'` combined with `B'`'s density in `U` forces
`≥ (δ⁵/2¹²)|A|²` length-3 paths through every `(a, b) ∈ A' × B'`. References:
Fox-Sudakov, *Dependent Random Choice* (2011), Lemma 5.2; Tao-Vu, *Additive
Combinatorics*, §6.4, Cor. 6.20.
-/
lemma dense_bipartite_has_path3_rectangle {G : Type*} [AddCommGroup G] [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        (δ^5 / 2^12) * (A.card : ℝ)^2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  -- The Fox-Sudakov DRC payload is packaged in `graph_dependentRandomChoice_payoff_pointwise`,
  -- which assembles `graph_pair_dependentRandomChoice`, `graph_high_degree_subset_lb`, and the
  -- final pointwise path-3 count step (see those lemmas for the breakdown).
  exact graph_dependentRandomChoice_payoff_pointwise δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense

/--
**Graph-BSG step C (length-3 path multiplicity).** Substantive content of the
Balog-Szemerédi-Gowers reduction. Given finite sets `A`, `B` of equal
cardinality `n`, a dense bipartite graph `E ⊆ A ×ˢ B` with `|E| ≥ δ · n²`,
and the *restricted sumset* `S := {a+b : (a,b) ∈ E}` of size `|S| ≤ K · n`,
there exist subsets `A' ⊆ A`, `B' ⊆ B` of size `≥ c(δ,K) · n` each whose
ordinary sumset is small: `|A' + B'| ≤ C(δ,K) · n`.

The mechanism is the length-3 path argument with multiplicity denominator: for
`a ∈ A'`, `b ∈ B'`, length-3 paths `a — b₁ — a₁ — b` in `E` give
representations `a + b = (a + b₁) − (a₁ + b₁) + (a₁ + b)` with all three
terms in `S`. Each pair `(a, b)` admits `Ω(δ^O(1) · n²)` such paths by
Cauchy-Schwarz on `E`. The cubic support count `|S − S + S| ≤ |S|³ ≤ K³ n³`
divided by the path-multiplicity lower bound yields the linear bound.

The key ingredient is to count length-3 paths *with multiplicity*: counting
only the support of the representation set (rather than multiplicity) is
insufficient. Tao–Vu §6.4 (proof of Theorem 2.29) / Petridis 2012.
-/
lemma graph_balogSzemerediGowers_restricted_sumset {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ δ K : ℝ, 0 < δ → 0 < K → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ A B : Finset G, A.Nonempty → B.Nonempty → A.card = B.card →
        ∀ E : Finset (G × G), E ⊆ A ×ˢ B →
          δ * (A.card : ℝ) ^ 2 ≤ (E.card : ℝ) →
          ((E.image (fun p ↦ p.1 + p.2)).card : ℝ) ≤ K * (A.card : ℝ) →
          ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
            c * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
            c * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
            ((A' + B').card : ℝ) ≤ C * (A.card : ℝ) := by
  -- ## High-level proof structure (length-3 path multiplicity argument).
  --
  -- Constants:
  -- * c := δ / 8 (from `dense_bipartite_has_path3_rectangle`, Fox-Sudakov DRC).
  -- * C := 2^13 K³ / δ^5 + 2^12 / δ^5, the path-multiplicity bound,
  --   absorbing both the M ≥ 1 and M = 0 sub-cases (triple-counting step in
  --   the proof of Tao-Vu Theorem 2.29, §6.4).
  intro δ K hδ hK
  refine ⟨δ / 8, 2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5,
    by positivity, by positivity, ?_⟩
  intro A B hA hB hAB E hE_sub hE_lb hS_ub
  -- Local abbreviations.
  set n : ℕ := A.card with hn_def
  have hn_pos : 0 < n := hA.card_pos
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_real_pos
  have hBcard_nat : B.card = n := hAB.symm
  have hBcard : (B.card : ℝ) = (n : ℝ) := by exact_mod_cast hBcard_nat
  -- Compose the three sub-lemmas: `dense_bipartite_has_path3_rectangle` for
  -- the pointwise path-3 lower bound, `path3_count_le_triple_rep_count` for
  -- the path-to-triple-rep bridge, `restricted_sumset_via_multiplicity` for
  -- the cubic divisor. The Apop/Bpop scaffolding that previously prefixed
  -- this proof has been deleted; DRC supplies its own A', B' refinement.
  -- We must first handle the degenerate case `δ > 1`, which is vacuous
  -- since `δ · n² ≤ |E| ≤ n²`.
  by_cases hδ_le : δ ≤ 1
  · -- ### Substantive case: δ ≤ 1. Compose the three sub-lemmas.
    -- Restricted sumset image S.
    set S : Finset G := E.image (fun p ↦ p.1 + p.2) with hS_def
    have hSdef : ∀ p ∈ E, p.1 + p.2 ∈ S := by
      intro p hp; exact Finset.mem_image_of_mem _ hp
    -- Convert hE_lb : δ · n² ≤ |E| to the rectangle form δ · |A| · |B| ≤ |E|.
    have hE_lb_rect : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ) := by
      have hsq : δ * (A.card : ℝ) ^ 2 = δ * (A.card : ℝ) * (B.card : ℝ) := by
        rw [hBcard, hn_def]; ring
      linarith [hE_lb, hsq.le, hsq.symm.le]
    -- Apply DRC pointwise path-3 rectangle.
    obtain ⟨A', B', hA'_sub, hB'_sub, hA'_card, hB'_card, hP_lb⟩ :=
      dense_bipartite_has_path3_rectangle δ hδ hδ_le A B hA hAB E hE_sub hE_lb_rect
    -- Set the integer floor multiplicity M.
    set M : ℕ := Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) with hM_def
    have hM_arg_nn : 0 ≤ (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 := by positivity
    have hM_floor_le : (M : ℝ) ≤ (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 :=
      Nat.floor_le hM_arg_nn
    have hM_floor_ge : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 - 1 < (M : ℝ) := by
      have h : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 <
          (Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) : ℝ) + 1 :=
        Nat.lt_floor_add_one ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2)
      have hMeq : (M : ℝ) = (Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) : ℝ) := by
        rfl
      rw [hMeq]; linarith
    -- Pointwise lower bound on the triple-rep count via the path-3 bridge.
    have hM_cover : ∀ a ∈ A', ∀ b ∈ B',
        M ≤ ((S ×ˢ S ×ˢ S).filter
              (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)).card := by
      intro a ha b hb
      have hP : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) :=
        hP_lb a ha b hb
      have hP_n : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
        rw [hn_def]; exact hP
      have hbridge : (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ)
          ≤ ((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card :=
        path3_count_le_triple_rep_count A B S E hSdef a b
      have hbridge_R : (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ)
          ≤ (((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card : ℝ) := by
        exact_mod_cast hbridge
      have hMR : (M : ℝ) ≤ (((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card : ℝ) :=
        le_trans hM_floor_le (le_trans hP_n hbridge_R)
      exact_mod_cast hMR
    -- Apply restricted-sumset-via-multiplicity to obtain M · |A'+B'| ≤ |S|^3.
    have hMS3 : M * (A' + B').card ≤ S.card ^ 3 :=
      restricted_sumset_via_multiplicity A' B' S M hM_cover
    have hMS3_R : (M : ℝ) * ((A' + B').card : ℝ) ≤ ((S.card : ℝ)) ^ 3 := by
      have h := hMS3
      have hh : ((M * (A' + B').card : ℕ) : ℝ) ≤ ((S.card ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast h
      push_cast at hh; exact hh
    -- Bound |S|^3 ≤ K^3 · n^3.
    have hS_card_nn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hSn_ub : (S.card : ℝ) ≤ K * (n : ℝ) := by
      have := hS_ub; rw [hn_def]; exact this
    have hSn_cube_ub : (S.card : ℝ) ^ 3 ≤ K ^ 3 * (n : ℝ) ^ 3 := by
      have h2 : (S.card : ℝ) ^ 3 ≤ (K * (n : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hS_card_nn hSn_ub 3
      have heq : (K * (n : ℝ)) ^ 3 = K ^ 3 * (n : ℝ) ^ 3 := by ring
      rw [heq] at h2; exact h2
    -- Combine: M · |A' + B'| ≤ K^3 · n^3.
    have hMSc : (M : ℝ) * ((A' + B').card : ℝ) ≤ K ^ 3 * (n : ℝ) ^ 3 :=
      le_trans hMS3_R hSn_cube_ub
    -- Refine to existential. The c · n bounds are exactly hA'_card, hB'_card
    -- since c = δ / 8 matches what DRC gave us; the |A' + B'| ≤ C · n bound
    -- requires case-splitting on M.
    refine ⟨A', B', hA'_sub, hB'_sub, ?_, ?_, ?_⟩
    · -- (δ/8) · |A| ≤ |A'|
      have h := hA'_card
      rw [hn_def]; exact h
    · -- (δ/8) · |A| ≤ |B'|
      have h := hB'_card
      rw [hn_def]; exact h
    · -- |A' + B'| ≤ C · n
      -- Two sub-cases: M = 0 or M ≥ 1.
      -- Constants we'll absorb into the final C = 2^13 K^3 / δ^5 + 2^12 / δ^5.
      have hδ5_pos : (0 : ℝ) < δ ^ 5 := by positivity
      have h2pow12_pos : (0 : ℝ) < (2 : ℝ) ^ 12 := by positivity
      have h2pow13_pos : (0 : ℝ) < (2 : ℝ) ^ 13 := by positivity
      have hK3_pos : (0 : ℝ) < K ^ 3 := by positivity
      have h_AplusB_nn : (0 : ℝ) ≤ ((A' + B').card : ℝ) := Nat.cast_nonneg _
      have hConstC_nn : (0 : ℝ) ≤ 2 ^ 12 / δ ^ 5 := by positivity
      have hConstC1_nn : (0 : ℝ) ≤ 2 ^ 13 * K ^ 3 / δ ^ 5 := by positivity
      by_cases hM_zero : M = 0
      · -- M = 0 ⇒ (δ^5 / 2^12) · n² < 1 ⇒ n² < 2^12 / δ^5.
        have hM0R : (M : ℝ) = 0 := by exact_mod_cast hM_zero
        have hsmall : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 < 1 := by
          have h := hM_floor_ge; rw [hM0R] at h; linarith
        have hn2_ub : (n : ℝ) ^ 2 < 2 ^ 12 / δ ^ 5 := by
          have hpow_inv : (0 : ℝ) < 2 ^ 12 / δ ^ 5 := by positivity
          have hh : (n : ℝ) ^ 2 = ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) * (2 ^ 12 / δ ^ 5) := by
            field_simp
          rw [hh]
          have h_ineq : ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) * (2 ^ 12 / δ ^ 5) <
              1 * (2 ^ 12 / δ ^ 5) :=
            mul_lt_mul_of_pos_right hsmall hpow_inv
          linarith
        -- Crude bound: |A'+B'| ≤ |A'|·|B'| ≤ n·n = n².
        have hAplusB_le_prod : (A' + B').card ≤ A'.card * B'.card :=
          Finset.card_add_le
        have hA'_le_n : A'.card ≤ n := by
          have := Finset.card_le_card hA'_sub
          rw [← hn_def] at this; exact this
        have hB'_le_n : B'.card ≤ n := by
          have := Finset.card_le_card hB'_sub
          rw [hBcard_nat] at this; exact this
        have hA'B'_le_n2_nat : A'.card * B'.card ≤ n * n := by
          exact Nat.mul_le_mul hA'_le_n hB'_le_n
        have hAplusB_le_n2 : (A' + B').card ≤ n * n :=
          le_trans hAplusB_le_prod hA'B'_le_n2_nat
        have hAplusB_le_n2R : ((A' + B').card : ℝ) ≤ (n : ℝ) ^ 2 := by
          have h : ((A' + B').card : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hAplusB_le_n2
          push_cast at h
          have heq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
          linarith
        have hAplusB_lt_const : ((A' + B').card : ℝ) < 2 ^ 12 / δ ^ 5 :=
          lt_of_le_of_lt hAplusB_le_n2R hn2_ub
        -- Now 2^12/δ^5 ≤ (2^12/δ^5) · n since 1 ≤ n.
        have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        have hconst_le : 2 ^ 12 / δ ^ 5 ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          have := mul_le_mul_of_nonneg_left hn_ge_one hConstC_nn
          simpa using this
        have hAplusB_le_constn : ((A' + B').card : ℝ) ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) :=
          le_trans (le_of_lt hAplusB_lt_const) hconst_le
        -- Combine: 2^12/δ^5 · n ≤ (2^13 K^3 / δ^5 + 2^12 / δ^5) · n.
        have hsum_expand : (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) =
            (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) + (2 ^ 12 / δ ^ 5) * (n : ℝ) := by ring
        have hC1n_nn : 0 ≤ (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) :=
          mul_nonneg hConstC1_nn hn_nn
        have hcomb : (2 ^ 12 / δ ^ 5) * (n : ℝ) ≤
            (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          rw [hsum_expand]; linarith
        linarith
      · -- M ≥ 1. Then M + 1 ≤ 2M, hence 2M > (δ^5/2^12)·n², so M > (δ^5/2^13)·n².
        have hM_ge_one : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM_zero
        have hM_geR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_one
        have hM_pos_R : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le zero_lt_one hM_geR
        have h_two_M : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 ≤ 2 * (M : ℝ) := by
          have h1 := hM_floor_ge -- (δ^5/2^12)·n² - 1 < M
          linarith
        have h_M_lower : (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 ≤ (M : ℝ) := by
          have h_div : (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 =
              ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) / 2 := by ring
          rw [h_div]; linarith
        -- Multiply the lower bound on M by |A'+B'|:
        -- (δ^5/2^13)·n² · |A'+B'| ≤ M · |A'+B'| ≤ K^3 · n^3.
        have h_mul1 : ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((A' + B').card : ℝ) ≤
            (M : ℝ) * ((A' + B').card : ℝ) := by
          exact mul_le_mul_of_nonneg_right h_M_lower h_AplusB_nn
        have h_chain : ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((A' + B').card : ℝ) ≤
            K ^ 3 * (n : ℝ) ^ 3 := le_trans h_mul1 hMSc
        -- Divide by (δ^5/2^13)·n² > 0 to get |A'+B'| ≤ (2^13 K^3 / δ^5) · n.
        have h_div_pos : (0 : ℝ) < (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 := by positivity
        have hδ5_ne : (δ ^ 5 : ℝ) ≠ 0 := ne_of_gt hδ5_pos
        have h_target_eq : K ^ 3 * (n : ℝ) ^ 3 =
            ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ)) := by
          rw [show ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ)) =
              (δ ^ 5 / δ ^ 5) * (K ^ 3 * (n : ℝ) ^ 3) by ring]
          rw [div_self hδ5_ne, one_mul]
        rw [h_target_eq] at h_chain
        have h_AplusB_le_lin : ((A' + B').card : ℝ) ≤ (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) :=
          le_of_mul_le_mul_left h_chain h_div_pos
        -- Absorb into C.
        have hC2n_nn : 0 ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) := mul_nonneg hConstC_nn hn_nn
        have h_final_const_ineq :
            (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) ≤
              (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          have hexpand : (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) =
              (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) + (2 ^ 12 / δ ^ 5) * (n : ℝ) := by ring
          rw [hexpand]; linarith
        linarith
  · -- ### Vacuous case: δ > 1. Then |E| ≤ n² but δ·n² ≤ |E|, contradiction.
    exfalso
    push Not at hδ_le  -- 1 < δ
    have hE_le_AB : E.card ≤ (A ×ˢ B).card := Finset.card_le_card hE_sub
    have hAB_card : (A ×ˢ B).card = n * n := by
      rw [Finset.card_product, ← hn_def, hBcard_nat]
    have hE_le_n2_nat : E.card ≤ n * n := by rw [← hAB_card]; exact hE_le_AB
    have hE_le_n2 : (E.card : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h : ((E.card : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hE_le_n2_nat
      push_cast at h
      have heq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
      linarith
    have hδn2 : δ * (n : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      have h := hE_lb; rw [hn_def]; exact h
    -- So δ · n² ≤ n², hence δ ≤ 1 (since n² > 0), contradicting 1 < δ.
    have hn2_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hδ_le_one : δ ≤ 1 := by
      have h1 : δ * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := le_trans hδn2 hE_le_n2
      have h2 : δ * (n : ℝ) ^ 2 ≤ 1 * (n : ℝ) ^ 2 := by linarith
      exact le_of_mul_le_mul_right h2 hn2_pos
    linarith

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

/-- Uniformly in three point sets of the same size, a positive fraction of
all sums cannot land in the third set when the first set has no five collinear. -/
theorem sparse_restricted_sums (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ A B C : Finset E, N ≤ A.card → B.card = A.card → C.card ≤ A.card →
      NoFiveCollinear (A : Set E) →
      (((A ×ˢ B).filter (fun p => p.1 + p.2 ∈ C)).card : ℝ) < ε * (A.card : ℝ)^2 := by
  classical
  obtain ⟨c, D, hc, hD, hgraph⟩ :=
    Finset.graph_balogSzemerediGowers_restricted_sumset (G := E) ε 1 hε zero_lt_one
  obtain ⟨K, hK⟩ := exists_nat_gt ((D / c)^2)
  obtain ⟨M, hM⟩ := unbounded_difference_growth (E := E) K
  obtain ⟨N, hN⟩ := exists_nat_gt ((M+1 : ℕ) / c : ℝ)
  refine ⟨max 1 N, ?_⟩
  intro A B C hn hB hC hA
  by_contra! hdense
  have han : 0 < A.card := (le_max_left 1 N).trans hn
  have hbn : 0 < B.card := hB ▸ han
  let E := (A ×ˢ B).filter (fun p => p.1 + p.2 ∈ C)
  have hsum : E.image (fun p => p.1 + p.2) ⊆ C := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hp).2
  obtain ⟨U, V, hU, _, hUs, hVs, hUV⟩ := hgraph A B
    (Finset.card_pos.mp han) (Finset.card_pos.mp hbn) hB.symm E (Finset.filter_subset ..) hdense
    (by simpa only [one_mul] using
      (show ((E.image (fun p => p.1+p.2)).card : ℝ) ≤ A.card by
        exact_mod_cast (Finset.card_le_card hsum).trans hC))
  have hMN : ((M+1 : ℕ) : ℝ) < N * c := (div_lt_iff₀ hc).mp hN
  have hNA : (N : ℝ) ≤ A.card := by exact_mod_cast (le_max_right 1 N).trans hn
  have hMU : M ≤ U.card := by
    have h := mul_le_mul_of_nonneg_right hNA hc.le
    push_cast at hMN
    exact_mod_cast (show (M : ℝ) ≤ U.card by linarith)
  have hlow := hM U hMU (fun T hT => hA T (hT.trans (Finset.coe_subset.mpr hU)))
  have hanR : 0 < (A.card : ℝ) := by exact_mod_cast han
  have hR : ((U-U).card : ℝ) * V.card ≤ ((U+V).card : ℝ)^2 := by
    simpa [sq] using (show ((U-U).card : ℝ) * V.card ≤
      ((U+V).card : ℝ) * (U+V).card by
      exact_mod_cast Finset.ruzsa_triangle_inequality_sub_add_add U V U)
  have hupper : ((U-U).card : ℝ) * (c * A.card) ≤ (D * A.card)^2 :=
    (mul_le_mul_of_nonneg_left hVs (by positivity)).trans
      (hR.trans (pow_le_pow_left₀ (by positivity) hUV 2))
  have hbound : ((U-U).card : ℝ) ≤ D^2 / c * A.card := by
    apply le_of_mul_le_mul_right _ (show 0 < c * (A.card : ℝ) by positivity)
    calc
      _ ≤ _ := hupper
      _ = _ := by field_simp
  have hfinal : ((U-U).card : ℝ) ≤ K * (U.card : ℝ) := calc
    _ ≤ D^2 / c * A.card := hbound
    _ = (D/c)^2 * (c * A.card) := by field_simp
    _ ≤ _ := mul_le_mul hK.le hUs (by positivity) (by positivity)
  exact (not_lt_of_ge (show (U-U).card ≤ K*U.card by exact_mod_cast hfinal)) hlow

end VectorSpace

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
