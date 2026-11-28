import OMAReductions.R_Green91_green_91_variants_all_friendly_R1

/-!
Reduction of `Green91.green_91.variants.all_friendly.R1.H1` (almost-sure existence of a bisection
with friendliness margin at least 2 in `G(2m, 1/2)`, Minzer-Sah-Sawhney, *Ann. Probab.* 52 (2024),
Theorem 1.3) to the two core MSS24 stages via microcanonical edge-slice conditioning:

- `H1`: Minzer-Sah-Sawhney (2024), Sections 3-5: inside every typical microcanonical edge-count
  slice `|2 k - choose (2m) 2| <= m^(5/4)`, all but an `epsilon`-fraction of graphs possess a
  bisection `s_0` (`s_0.card = m`) whose vertices outside an exceptional set `U` of size at most
  `m^(1/4)` all have friendliness at least `(1/10) * sqrt (2m)`.
- `H2`: Minzer-Sah-Sawhney (2024), Section 6: local expansion switching repair upgrades an almost-
  everywhere `(1/10) * sqrt (2m)`-friendly bisection (with at most `m^(1/4)` exceptional vertices)
  to a globally `>= 2`-friendly bisection outside an `epsilon`-fraction of all graphs on `2m`
  vertices.

In `main` and the private lemmas below, we prove completely in Lean 4:
1. Explicit edge-set equivalence `SimpleGraph (Fin n) ~= Finset {e : Sym2 (Fin n) // e in diagSet^c}`
   preserving `edgeFinset.card` and proving `Fintype.card (SimpleGraph (Fin n)) = 2^(n.choose 2)`.
2. Exact measure-to-counting bridge showing `Green91.prob n P` equals the uniform `ENNReal` graph
   ratio `((univ.filter P).card : ENNReal) / 2^(n.choose 2)`.
3. Exact binomial edge-count variance identity
   `sum_{G} (2 * G.edgeFinset.card - n.choose 2)^2 = n.choose 2 * 2^(n.choose 2)` proved by
   induction on `N` via `(x + 1)^2 + (x - 1)^2 = 2 * x^2 + 2`, yielding the Chebyshev tail bound
   `<= (2 / sqrt m) * 2^((2m).choose 2)` outside the microcanonical window `|2k - N| <= m^(5/4)`.
4. Fiberwise edge-slice union bound combining Chebyshev concentration, `H1`, and `H2`, and
   `ENNReal` order-topology glue proving `Filter.Tendsto ... Filter.atTop (nhds 1)`.
-/

open scoped Classical

namespace OMA.R_Green91_green_91_variants_all_friendly_R1_H1_R1

/- Minzer-Sah-Sawhney (2024, Sections 3-5): microcanonical conditioned second-moment existence of a
(1/10)*sqrt(2m)-friendly bisection outside at most m^(1/4) exceptional vertices. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ k : ℕ,
    |(2 : ℝ) * (k : ℝ) - ((2 * m).choose 2 : ℝ)| ≤ (m : ℝ) ^ (5 / 4 : ℝ) →
    ((((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
      (fun G => G.edgeFinset.card = k ∧
        ¬ ∃ s₀ U : Finset (Fin (2 * m)),
            s₀.card = m ∧ (U.card : ℝ) ≤ (m : ℝ) ^ (1 / 4 : ℝ) ∧
            ∀ v : Fin (2 * m), v ∉ U →
              (1 / 10 : ℝ) * Real.sqrt (2 * m) ≤ (Green91.friendliness G s₀ v : ℝ))).card : ℝ) ≤
      ε * (((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
        (fun G => G.edgeFinset.card = k)).card : ℝ))

/- Minzer-Sah-Sawhney (2024, Section 6): local expansion switching repair of at most m^(1/4)
exceptional vertices from a (1/10)*sqrt(2m)-friendly bisection into a globally >= 2-friendly
bisection. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
    ((((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
      (fun G =>
        (∃ s₀ U : Finset (Fin (2 * m)),
            s₀.card = m ∧ (U.card : ℝ) ≤ (m : ℝ) ^ (1 / 4 : ℝ) ∧
            ∀ v : Fin (2 * m), v ∉ U →
              (1 / 10 : ℝ) * Real.sqrt (2 * m) ≤ (Green91.friendliness G s₀ v : ℝ)) ∧
        ¬ ∃ s : Finset (Fin (2 * m)),
            s.card = m ∧ ∀ v : Fin (2 * m), 2 ≤ Green91.friendliness G s v)).card : ℝ) ≤
      ε * (2 : ℝ) ^ ((2 * m).choose 2))

section

private noncomputable def graphEquivFinsetEdges (n : ℕ) :
    SimpleGraph (Fin n) ≃ Finset {e : Sym2 (Fin n) // e ∈ Sym2.diagSetᶜ} where
  toFun G := Finset.univ.filter fun e => e.1 ∈ G.edgeSet
  invFun S := SimpleGraph.fromEdgeSet
    (Subtype.val '' (S : Set {e : Sym2 (Fin n) // e ∈ Sym2.diagSetᶜ}))
  left_inv G := by
    have hset : Subtype.val '' ((Finset.univ.filter fun e : {e : Sym2 (Fin n) // e ∈ Sym2.diagSetᶜ} =>
        e.1 ∈ G.edgeSet) : Set {e : Sym2 (Fin n) // e ∈ Sym2.diagSetᶜ}) = G.edgeSet := by
      ext e
      simp only [Set.mem_image, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨e', _⟩, he', rfl⟩
        exact he'
      · intro he
        have hnd : e ∈ Sym2.diagSetᶜ := G.not_isDiag_of_mem_edgeSet he
        exact ⟨⟨e, hnd⟩, he, rfl⟩
    change SimpleGraph.fromEdgeSet
      (Subtype.val '' ((Finset.univ.filter fun e : {e : Sym2 (Fin n) // e ∈ Sym2.diagSetᶜ} =>
        e.1 ∈ G.edgeSet) : Set {e : Sym2 (Fin n) // e ∈ Sym2.diagSetᶜ})) = G
    rw [hset, SimpleGraph.fromEdgeSet_edgeSet]
  right_inv S := by
    ext ⟨e, he⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.edgeSet_fromEdgeSet,
      Set.mem_sdiff, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨⟨⟨e', he'⟩, hS, hEq⟩, _⟩
      have hsub : (⟨e', he'⟩ : {x : Sym2 (Fin n) // x ∈ Sym2.diagSetᶜ}) = ⟨e, he⟩ :=
        Subtype.ext hEq
      rwa [← hsub]
    · intro hS
      exact ⟨⟨⟨e, he⟩, hS, rfl⟩, he⟩

private lemma card_graphEquivFinsetEdges (n : ℕ) (G : SimpleGraph (Fin n)) :
    (graphEquivFinsetEdges n G).card = G.edgeFinset.card := by
  have himg : (graphEquivFinsetEdges n G).image Subtype.val = G.edgeFinset := by
    ext e
    simp only [Finset.mem_image, graphEquivFinsetEdges, Equiv.coe_fn_mk, Finset.mem_filter,
      Finset.mem_univ, true_and, SimpleGraph.mem_edgeFinset]
    constructor
    · rintro ⟨⟨e', _⟩, he', rfl⟩
      exact he'
    · intro he
      exact ⟨⟨e, G.not_isDiag_of_mem_edgeSet he⟩, he, rfl⟩
  rw [← himg, Finset.card_image_of_injective _ Subtype.val_injective]

private lemma card_nonDiag_sym2 (n : ℕ) :
    Fintype.card {e : Sym2 (Fin n) // e ∈ Sym2.diagSetᶜ} = n.choose 2 := by
  rw [Sym2.card_diagSet_compl, Fintype.card_fin]

private lemma card_simpleGraph_fin (n : ℕ) :
    Fintype.card (SimpleGraph (Fin n)) = 2 ^ (n.choose 2) := by
  rw [Fintype.card_congr (graphEquivFinsetEdges n), Fintype.card_finset, card_nonDiag_sym2]

private lemma edgeFinset_card_le_choose (n : ℕ) (G : SimpleGraph (Fin n)) :
    G.edgeFinset.card ≤ n.choose 2 := by
  rw [← card_graphEquivFinsetEdges n G, ← card_nonDiag_sym2 n]
  exact Finset.card_le_univ _

private lemma binomialRandom_half_singleton (n : ℕ) (G : SimpleGraph (Fin n)) :
    SimpleGraph.binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩ {G} =
      ((2 : ENNReal) ^ (n.choose 2))⁻¹ := by
  let p : unitInterval := ⟨1 / 2, by norm_num⟩
  change SimpleGraph.binomialRandom (Fin n) p {G} = ((2 : ENNReal) ^ (n.choose 2))⁻¹
  rw [SimpleGraph.binomialRandom_singleton]
  have hp_symm : unitInterval.symm p = p := by
    apply Subtype.ext
    change (1 : ℝ) - 1 / 2 = 1 / 2
    norm_num
  rw [hp_symm]
  have hncard_eq : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hnat_card : Nat.card (Fin n) = n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hncard_eq, hnat_card]
  have hle : G.edgeFinset.card ≤ n.choose 2 := edgeFinset_card_le_choose n G
  rw [← pow_add, Nat.add_sub_of_le hle]
  have h2nn : unitInterval.toNNReal p * 2 = 1 := by
    apply NNReal.eq
    change (1 / 2 : ℝ) * 2 = 1
    norm_num
  have h2e : (unitInterval.toNNReal p : ENNReal) * 2 = 1 := by
    exact_mod_cast h2nn
  have hp_inv : (unitInterval.toNNReal p : ENNReal) = (2 : ENNReal)⁻¹ := by
    calc (unitInterval.toNNReal p : ENNReal)
        = (unitInterval.toNNReal p : ENNReal) * (2 * (2 : ENNReal)⁻¹) := by
            rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
      _ = ((unitInterval.toNNReal p : ENNReal) * 2) * (2 : ENNReal)⁻¹ := by rw [mul_assoc]
      _ = (2 : ENNReal)⁻¹ := by rw [h2e, one_mul]
  rw [hp_inv, ENNReal.inv_pow]

private lemma green91_prob_eq_card_div (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    Green91.prob n P =
      (((Finset.univ : Finset (SimpleGraph (Fin n))).filter P).card : ENNReal) /
        (2 : ENNReal) ^ (n.choose 2) := by
  unfold Green91.prob
  have hset : ({G : SimpleGraph (Fin n) | P G} : Set (SimpleGraph (Fin n))) =
      ⋃ G ∈ (Finset.univ : Finset (SimpleGraph (Fin n))).filter P, ({G} : Set _) := by
    ext G
    simp
  have hdisj : Set.PairwiseDisjoint
      (((Finset.univ : Finset (SimpleGraph (Fin n))).filter P) : Set (SimpleGraph (Fin n)))
      (fun G : SimpleGraph (Fin n) => ({G} : Set (SimpleGraph (Fin n)))) := by
    intro G₁ _ G₂ _ hne
    exact Set.disjoint_singleton.mpr hne
  have hmeas : ∀ G : SimpleGraph (Fin n), MeasurableSet ({G} : Set (SimpleGraph (Fin n))) := by
    intro G
    have hpre : ({G} : Set (SimpleGraph (Fin n))) = SimpleGraph.edgeSet ⁻¹' {G.edgeSet} := by
      ext H
      simp
    rw [hpre]
    exact (MeasurableSet.singleton G.edgeSet).preimage SimpleGraph.measurableEmbedding_edgeSet.measurable
  rw [hset, MeasureTheory.measure_biUnion_finset hdisj (fun G _ => hmeas G)]
  simp_rw [binomialRandom_half_singleton]
  rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

private noncomputable def finsetSuccEquiv (N : ℕ) :
    Finset (Fin N) × Bool ≃ Finset (Fin (N + 1)) where
  toFun p :=
    if p.2 then insert (Fin.last N) (p.1.map Fin.castSuccEmb)
    else p.1.map Fin.castSuccEmb
  invFun S :=
    (Finset.univ.filter fun i : Fin N => i.castSucc ∈ S, decide (Fin.last N ∈ S))
  left_inv := by
    rintro ⟨T, b⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · ext i
        simp [Finset.mem_map]
      · simp [Finset.mem_map, Fin.castSucc_ne_last]
    · simp only [↓reduceIte, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · ext i
        simp [Finset.mem_map, Fin.castSucc_ne_last]
      · simp
  right_inv S := by
    by_cases h : Fin.last N ∈ S
    · simp only [decide_eq_true_eq.mpr h, ↓reduceIte]
      ext x
      induction x using Fin.lastCases with
      | last => simp [h]
      | cast i => simp [Finset.mem_map, Fin.castSucc_ne_last]
    · simp only [decide_eq_false h, Bool.false_eq_true, ↓reduceIte]
      ext x
      induction x using Fin.lastCases with
      | last => simp [Finset.mem_map, Fin.castSucc_ne_last, h]
      | cast i => simp [Finset.mem_map]

private lemma sum_finset_card_variance (N : ℕ) :
    ∑ S : Finset (Fin N), ((2 : ℝ) * (S.card : ℝ) - (N : ℝ)) ^ 2 = (N : ℝ) * (2 : ℝ) ^ N := by
  induction N with
  | zero =>
    have hcard0 : ∀ S : Finset (Fin 0), S.card = 0 := fun S => by
      rw [Finset.eq_empty_of_isEmpty S]
      rfl
    simp [hcard0]
  | succ N ih =>
    rw [← Fintype.sum_equiv (finsetSuccEquiv N)
      (fun p => ((2 : ℝ) * ((finsetSuccEquiv N p).card : ℝ) - ((N + 1 : ℕ) : ℝ)) ^ 2)
      (fun S => ((2 : ℝ) * (S.card : ℝ) - ((N + 1 : ℕ) : ℝ)) ^ 2)
      (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    have hpair : ∀ T : Finset (Fin N),
        ∑ b : Bool, ((2 : ℝ) * ((finsetSuccEquiv N (T, b)).card : ℝ) - ((N + 1 : ℕ) : ℝ)) ^ 2 =
          2 * ((2 : ℝ) * (T.card : ℝ) - (N : ℝ)) ^ 2 + 2 := by
      intro T
      rw [Fintype.sum_bool]
      have hnotmem : Fin.last N ∉ T.map Fin.castSuccEmb := by
        simp [Finset.mem_map, Fin.castSucc_ne_last]
      have hcard_t : (finsetSuccEquiv N (T, true)).card = T.card + 1 := by
        simp [finsetSuccEquiv, Finset.card_insert_of_notMem hnotmem]
      have hcard_f : (finsetSuccEquiv N (T, false)).card = T.card := by
        simp [finsetSuccEquiv]
      rw [hcard_t, hcard_f]
      push_cast
      ring
    simp_rw [hpair]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ih, Finset.sum_const, Finset.card_univ,
      Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

private lemma sum_graph_edge_variance (n : ℕ) :
    ∑ G : SimpleGraph (Fin n),
        ((2 : ℝ) * (G.edgeFinset.card : ℝ) - (n.choose 2 : ℝ)) ^ 2 =
      (n.choose 2 : ℝ) * (2 : ℝ) ^ (n.choose 2) := by
  let α := {e : Sym2 (Fin n) // e ∈ Sym2.diagSetᶜ}
  let eα : α ≃ Fin (n.choose 2) := Fintype.equivFinOfCardEq (card_nonDiag_sym2 n)
  let eAll : SimpleGraph (Fin n) ≃ Finset (Fin (n.choose 2)) :=
    (graphEquivFinsetEdges n).trans (Equiv.finsetCongr eα)
  have hcard : ∀ G : SimpleGraph (Fin n), (eAll G).card = G.edgeFinset.card := by
    intro G
    dsimp only [eAll]
    rw [Equiv.trans_apply, Equiv.finsetCongr_apply, Finset.card_map, card_graphEquivFinsetEdges]
  rw [← sum_finset_card_variance (n.choose 2)]
  exact Fintype.sum_equiv eAll _ _ (fun G => by rw [hcard G])

private lemma choose_two_mul_le (m : ℕ) : ((2 * m).choose 2 : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by
  have hnat : (2 * m).choose 2 ≤ 2 * m ^ 2 := by
    rw [Nat.choose_two_right]
    have hmul : 2 * m * (2 * m - 1) ≤ 4 * m ^ 2 := by
      have hsub : 2 * m - 1 ≤ 2 * m := Nat.sub_le _ _
      calc 2 * m * (2 * m - 1) ≤ 2 * m * (2 * m) := Nat.mul_le_mul_left _ hsub
        _ = 4 * m ^ 2 := by ring
    omega
  exact_mod_cast hnat

private lemma atypical_edge_count_le (m : ℕ) (hm : 1 ≤ m) :
    ((((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
      (fun G => (m : ℝ) ^ (5 / 4 : ℝ) <
        |(2 : ℝ) * (G.edgeFinset.card : ℝ) - ((2 * m).choose 2 : ℝ)|)).card : ℝ) ≤
      (2 / Real.sqrt (m : ℝ)) * (2 : ℝ) ^ ((2 * m).choose 2)) := by
  let N := (2 * m).choose 2
  let bad := (Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
    (fun G => (m : ℝ) ^ (5 / 4 : ℝ) < |(2 : ℝ) * (G.edgeFinset.card : ℝ) - (N : ℝ)|)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := le_of_lt hm_pos
  have hsq_pow : ((m : ℝ) ^ (5 / 4 : ℝ)) ^ 2 = (m : ℝ) ^ 2 * Real.sqrt (m : ℝ) := by
    rw [← Real.rpow_natCast ((m : ℝ) ^ (5 / 4 : ℝ)) 2, ← Real.rpow_mul hm_nn]
    have hexp : (5 / 4 : ℝ) * (2 : ℕ) = (2 : ℝ) + (1 / 2 : ℝ) := by norm_num
    rw [hexp, Real.rpow_add hm_pos, Real.rpow_two, Real.sqrt_eq_rpow]
  have hmarkov : (bad.card : ℝ) * ((m : ℝ) ^ 2 * Real.sqrt (m : ℝ)) ≤
      (N : ℝ) * (2 : ℝ) ^ N := by
    calc (bad.card : ℝ) * ((m : ℝ) ^ 2 * Real.sqrt (m : ℝ))
        = ∑ _G ∈ bad, ((m : ℝ) ^ (5 / 4 : ℝ)) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, hsq_pow]
      _ ≤ ∑ G ∈ bad, ((2 : ℝ) * (G.edgeFinset.card : ℝ) - (N : ℝ)) ^ 2 := by
            refine Finset.sum_le_sum fun G hG => ?_
            have hlt : (m : ℝ) ^ (5 / 4 : ℝ) < |(2 : ℝ) * (G.edgeFinset.card : ℝ) - (N : ℝ)| :=
              (Finset.mem_filter.mp hG).2
            have h0 : (0 : ℝ) ≤ (m : ℝ) ^ (5 / 4 : ℝ) := Real.rpow_nonneg hm_nn _
            have hsq : ((m : ℝ) ^ (5 / 4 : ℝ)) ^ 2 ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ) - (N : ℝ)) ^ 2 := by
              rw [sq_le_sq, abs_of_nonneg h0]
              exact le_of_lt hlt
            exact hsq
      _ ≤ ∑ G : SimpleGraph (Fin (2 * m)),
            ((2 : ℝ) * (G.edgeFinset.card : ℝ) - (N : ℝ)) ^ 2 := by
            refine Finset.sum_le_univ_sum_of_nonneg fun G => sq_nonneg _
      _ = (N : ℝ) * (2 : ℝ) ^ N := sum_graph_edge_variance (2 * m)
  have hden_pos : (0 : ℝ) < (m : ℝ) ^ 2 * Real.sqrt (m : ℝ) :=
    mul_pos (pow_pos hm_pos 2) (Real.sqrt_pos.mpr hm_pos)
  have hN_le : (N : ℝ) * (2 : ℝ) ^ N ≤ (2 * (m : ℝ) ^ 2) * (2 : ℝ) ^ N :=
    mul_le_mul_of_nonneg_right (choose_two_mul_le m) (by positivity)
  have hcomb : (bad.card : ℝ) * ((m : ℝ) ^ 2 * Real.sqrt (m : ℝ)) ≤
      (2 * (m : ℝ) ^ 2) * (2 : ℝ) ^ N := hmarkov.trans hN_le
  have hdiv : (bad.card : ℝ) ≤
      ((2 * (m : ℝ) ^ 2) * (2 : ℝ) ^ N) / ((m : ℝ) ^ 2 * Real.sqrt (m : ℝ)) :=
    (le_div_iff₀ hden_pos).mpr hcomb
  have hsimp : ((2 * (m : ℝ) ^ 2) * (2 : ℝ) ^ N) / ((m : ℝ) ^ 2 * Real.sqrt (m : ℝ)) =
      (2 / Real.sqrt (m : ℝ)) * (2 : ℝ) ^ N := by
    have hm2_ne : (m : ℝ) ^ 2 ≠ 0 := ne_of_gt (pow_pos hm_pos 2)
    have hsq_ne : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hm_pos)
    field_simp [hm2_ne, hsq_ne]
  exact hdiv.trans_eq hsimp

private lemma sum_slice_cards_le (m : ℕ) (K : Finset ℕ) (hK : K ⊆ Finset.range ((2 * m).choose 2 + 1)) :
    ∑ k ∈ K,
      (((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
        (fun G => G.edgeFinset.card = k)).card : ℝ) ≤
      (2 : ℝ) ^ ((2 * m).choose 2) := by
  have hle_nat : ∑ k ∈ K,
      ((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
        (fun G => G.edgeFinset.card = k)).card ≤
      ∑ k ∈ Finset.range ((2 * m).choose 2 + 1),
      ((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
        (fun G => G.edgeFinset.card = k)).card :=
    Finset.sum_le_sum_of_subset hK
  have heq_nat : ∑ k ∈ Finset.range ((2 * m).choose 2 + 1),
      ((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
        (fun G => G.edgeFinset.card = k)).card =
      2 ^ ((2 * m).choose 2) := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := fun G : SimpleGraph (Fin (2 * m)) => G.edgeFinset.card)
      (fun G _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (edgeFinset_card_le_choose (2 * m) G)))]
    rw [Finset.card_univ, card_simpleGraph_fin]
  have hnat : ∑ k ∈ K,
      ((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
        (fun G => G.edgeFinset.card = k)).card ≤
      2 ^ ((2 * m).choose 2) := hle_nat.trans_eq heq_nat
  exact_mod_cast hnat

end

theorem main : H1 → H2 → OMA.R_Green91_green_91_variants_all_friendly_R1.H1 := by
  intro h1 h2
  rw [OMA.R_Green91_green_91_variants_all_friendly_R1.H1]
  rw [tendsto_order]
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha_ne_top : a ≠ ⊤ := ne_top_of_lt ha
    have ha_real_lt : a.toReal < 1 := by
      have h1_eq : (1 : ENNReal).toReal = 1 := by simp
      rw [← h1_eq]
      exact (ENNReal.toReal_lt_toReal ha_ne_top ENNReal.one_ne_top).mpr ha
    let ε : ℝ := (1 - a.toReal) / 2
    have hε_pos : 0 < ε := by dsimp only [ε]; linarith
    have hε3_pos : 0 < ε / 3 := by linarith
    obtain ⟨m₀, hm₀⟩ := h1 (ε / 3) hε3_pos
    obtain ⟨m₁, hm₁⟩ := h2 (ε / 3) hε3_pos
    let m₂ : ℕ := max 1 (Nat.ceil ((6 / ε) ^ 2))
    let M : ℕ := max (max m₀ m₁) m₂
    rw [Filter.eventually_atTop]
    refine ⟨M, fun m hm => ?_⟩
    have hm_ge0 : m₀ ≤ m := le_trans (le_trans (le_max_left m₀ m₁) (le_max_left _ m₂)) hm
    have hm_ge1 : m₁ ≤ m := le_trans (le_trans (le_max_right m₀ m₁) (le_max_left _ m₂)) hm
    have hm_ge2 : m₂ ≤ m := le_trans (le_max_right _ m₂) hm
    have hm_one : 1 ≤ m := le_trans (le_max_left _ _) hm_ge2
    let N : ℕ := (2 * m).choose 2
    let Good : SimpleGraph (Fin (2 * m)) → Prop := fun G =>
      ∃ s : Finset (Fin (2 * m)), s.card = m ∧ ∀ v : Fin (2 * m), 2 ≤ Green91.friendliness G s v
    let AlmostGood : SimpleGraph (Fin (2 * m)) → Prop := fun G =>
      ∃ s₀ U : Finset (Fin (2 * m)),
        s₀.card = m ∧ (U.card : ℝ) ≤ (m : ℝ) ^ (1 / 4 : ℝ) ∧
        ∀ v : Fin (2 * m), v ∉ U →
          (1 / 10 : ℝ) * Real.sqrt (2 * m) ≤ (Green91.friendliness G s₀ v : ℝ)
    let Typical : SimpleGraph (Fin (2 * m)) → Prop := fun G =>
      |(2 : ℝ) * (G.edgeFinset.card : ℝ) - (N : ℝ)| ≤ (m : ℝ) ^ (5 / 4 : ℝ)
    let BadAll := (Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter (fun G => ¬ Good G)
    let Bad₁ := (Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter (fun G => ¬ Typical G)
    let Bad₂ := (Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter (fun G => Typical G ∧ ¬ AlmostGood G)
    let Bad₃ := (Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter (fun G => AlmostGood G ∧ ¬ Good G)
    have hBad_sub : BadAll ⊆ Bad₁ ∪ Bad₂ ∪ Bad₃ := by
      intro G hG
      have hnotG : ¬ Good G := (Finset.mem_filter.mp hG).2
      by_cases hT : Typical G
      · by_cases hA : AlmostGood G
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ G, hA, hnotG⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ G, hT, hA⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ G, hT⟩))
    have hBad_card : (BadAll.card : ℝ) ≤ (Bad₁.card : ℝ) + (Bad₂.card : ℝ) + (Bad₃.card : ℝ) := by
      have h12 : BadAll.card ≤ (Bad₁ ∪ Bad₂ ∪ Bad₃).card := Finset.card_le_card hBad_sub
      have h34 : (Bad₁ ∪ Bad₂ ∪ Bad₃).card ≤ (Bad₁ ∪ Bad₂).card + Bad₃.card := Finset.card_union_le _ _
      have h56 : (Bad₁ ∪ Bad₂).card ≤ Bad₁.card + Bad₂.card := Finset.card_union_le _ _
      have htot : BadAll.card ≤ Bad₁.card + Bad₂.card + Bad₃.card := by omega
      exact_mod_cast htot
    have hBad₁_le : (Bad₁.card : ℝ) ≤ (ε / 3) * (2 : ℝ) ^ N := by
      have hEq : Bad₁ = (Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
          (fun G => (m : ℝ) ^ (5 / 4 : ℝ) < |(2 : ℝ) * (G.edgeFinset.card : ℝ) - (N : ℝ)|) := by
        ext G
        simp only [Bad₁, Typical, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
      rw [hEq]
      have hcheb := atypical_edge_count_le m hm_one
      have h6le : (6 / ε) ^ 2 ≤ (m : ℝ) := by
        have hceil : (6 / ε) ^ 2 ≤ (Nat.ceil ((6 / ε) ^ 2) : ℝ) := Nat.le_ceil _
        have hcm : Nat.ceil ((6 / ε) ^ 2) ≤ m := le_trans (le_max_right _ _) hm_ge2
        exact hceil.trans (by exact_mod_cast hcm)
      have h6_pos : 0 < 6 / ε := by positivity
      have hsq_ge : 6 / ε ≤ Real.sqrt (m : ℝ) := by
        rw [← Real.sqrt_sq (le_of_lt h6_pos)]
        exact Real.sqrt_le_sqrt h6le
      have hsq_pos : 0 < Real.sqrt (m : ℝ) := lt_of_lt_of_le h6_pos hsq_ge
      have hfrac_le : 2 / Real.sqrt (m : ℝ) ≤ ε / 3 := by
        rw [div_le_iff₀ hsq_pos]
        have hmul : (ε / 3) * (6 / ε) = 2 := by field_simp [ne_of_gt hε_pos]; ring
        calc (2 : ℝ) = (ε / 3) * (6 / ε) := hmul.symm
          _ ≤ (ε / 3) * Real.sqrt (m : ℝ) := mul_le_mul_of_nonneg_left hsq_ge (le_of_lt hε3_pos)
      exact hcheb.trans (mul_le_mul_of_nonneg_right hfrac_le (by positivity))
    have hBad₂_le : (Bad₂.card : ℝ) ≤ (ε / 3) * (2 : ℝ) ^ N := by
      let K : Finset ℕ := (Finset.range (N + 1)).filter
        (fun k : ℕ => |(2 : ℝ) * (k : ℝ) - (N : ℝ)| ≤ (m : ℝ) ^ (5 / 4 : ℝ))
      have hsub : Bad₂ ⊆ K.biUnion (fun k =>
          (Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
            (fun G => G.edgeFinset.card = k ∧ ¬ AlmostGood G)) := by
        intro G hG
        obtain ⟨_, hT, hnotA⟩ := Finset.mem_filter.mp hG
        refine Finset.mem_biUnion.mpr ⟨G.edgeFinset.card, ?_, ?_⟩
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (edgeFinset_card_le_choose (2 * m) G)), hT⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ G, rfl, hnotA⟩
      have hcard_bi : (Bad₂.card : ℝ) ≤ ∑ k ∈ K,
          (((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
            (fun G => G.edgeFinset.card = k ∧ ¬ AlmostGood G)).card : ℝ) := by
        have hnat := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
        exact_mod_cast hnat
      have hsum_le : ∑ k ∈ K,
          (((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
            (fun G => G.edgeFinset.card = k ∧ ¬ AlmostGood G)).card : ℝ) ≤
          ∑ k ∈ K, (ε / 3) *
            (((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
              (fun G => G.edgeFinset.card = k)).card : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact hm₀ m hm_ge0 k (Finset.mem_filter.mp hk).2
      have hslice_le : ∑ k ∈ K,
          (((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
            (fun G => G.edgeFinset.card = k)).card : ℝ) ≤ (2 : ℝ) ^ N :=
        sum_slice_cards_le m K (Finset.filter_subset _ _)
      calc (Bad₂.card : ℝ)
          ≤ ∑ k ∈ K, (ε / 3) *
              (((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
                (fun G => G.edgeFinset.card = k)).card : ℝ) := hcard_bi.trans hsum_le
        _ = (ε / 3) * ∑ k ∈ K,
              (((Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter
                (fun G => G.edgeFinset.card = k)).card : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ (ε / 3) * (2 : ℝ) ^ N := mul_le_mul_of_nonneg_left hslice_le (le_of_lt hε3_pos)
    have hBad₃_le : (Bad₃.card : ℝ) ≤ (ε / 3) * (2 : ℝ) ^ N := hm₁ m hm_ge1
    have hBad_tot : (BadAll.card : ℝ) ≤ ε * (2 : ℝ) ^ N := by
      linarith
    let GoodSet := (Finset.univ : Finset (SimpleGraph (Fin (2 * m)))).filter Good
    have hcompl_card : (GoodSet.card : ℝ) + (BadAll.card : ℝ) = (2 : ℝ) ^ N := by
      have hdisj : Disjoint GoodSet BadAll :=
        Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
      have hunion : GoodSet ∪ BadAll = Finset.univ := by
        ext G
        simp [GoodSet, BadAll, em]
      have hnat : GoodSet.card + BadAll.card = 2 ^ N := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, card_simpleGraph_fin]
      exact_mod_cast hnat
    have hGood_ge : (1 - ε) * (2 : ℝ) ^ N ≤ (GoodSet.card : ℝ) := by linarith
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have hratio_ge : 1 - ε ≤ (GoodSet.card : ℝ) / (2 : ℝ) ^ N :=
      (le_div_iff₀ hpow_pos).mpr hGood_ge
    have ha_lt_ratio : a.toReal < (GoodSet.card : ℝ) / (2 : ℝ) ^ N := by
      have hlt : a.toReal < 1 - ε := by dsimp only [ε]; linarith
      exact lt_of_lt_of_le hlt hratio_ge
    have hratio_pos : 0 < (GoodSet.card : ℝ) / (2 : ℝ) ^ N :=
      lt_of_le_of_lt ENNReal.toReal_nonneg ha_lt_ratio
    have hofReal_lt : a < ENNReal.ofReal ((GoodSet.card : ℝ) / (2 : ℝ) ^ N) := by
      rw [← ENNReal.ofReal_toReal ha_ne_top]
      exact (ENNReal.ofReal_lt_ofReal_iff hratio_pos).mpr ha_lt_ratio
    have hofReal_eq : ENNReal.ofReal ((GoodSet.card : ℝ) / (2 : ℝ) ^ N) = Green91.prob (2 * m) Good := by
      rw [green91_prob_eq_card_div (2 * m) Good, ENNReal.ofReal_div_of_pos hpow_pos,
        ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      apply congrArg (fun k : ℕ => (k : ENNReal) / (2 : ENNReal) ^ N)
      apply congrArg Finset.card
      ext G
      simp [GoodSet]
    exact hofReal_lt.trans_eq hofReal_eq
  · intro b hb
    refine Filter.Eventually.of_forall fun m => ?_
    have hle : Green91.prob (2 * m) (fun G =>
        ∃ s : Finset (Fin (2 * m)), s.card = m ∧ ∀ v, 2 ≤ Green91.friendliness G s v) ≤ 1 := by
      unfold Green91.prob
      exact MeasureTheory.prob_le_one
    exact lt_of_le_of_lt hle hb

end OMA.R_Green91_green_91_variants_all_friendly_R1_H1_R1
