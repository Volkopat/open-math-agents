import FormalConjectures.Wikipedia.SidorenkoConjecture

/-!
# Sidorenko's Inequality for Complete Bipartite Graphs (Graphon Version)

Proof that every complete bipartite graph `K_{A, B}` satisfies Sidorenko's inequality
`graphonEdgeDensity W ^ e(K_{A, B}) ≤ graphonHomDensity K_{A, B} W` for every graphon `W`,
using Fubini's theorem on product spaces and two applications of Jensen's inequality.
-/

-- Problem: Sidorenko's conjecture (1993)
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/SidorenkoConjecture.lean:133 (declaration SidorenkoConjecture.sidorenko_completeBipartiteGraph_graphon)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Retains the proof from open-math-agents PR #274; uses the standard edge-set API.

open MeasureTheory MeasureTheory.Measure Finset SimpleGraph LimitObjects

private lemma edgeFinset_completeBipartiteGraph {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableRel (completeBipartiteGraph A B).Adj] :
    (completeBipartiteGraph A B).edgeFinset =
      Finset.univ.image (fun p : A × B => s(Sum.inl p.1, Sum.inr p.2)) := by
  apply Finset.coe_injective
  simpa using (SimpleGraph.edgeSet_completeBipartiteGraph (W₁ := A) (W₂ := B))

private lemma edgeMap_injective {A B : Type*} :
    Function.Injective (fun p : A × B => (s(Sum.inl p.1, Sum.inr p.2) : Sym2 (A ⊕ B))) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simpa [Sym2.eq_iff] using h

private lemma card_edgeFinset_completeBipartiteGraph {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableRel (completeBipartiteGraph A B).Adj] :
    (completeBipartiteGraph A B).edgeFinset.card = Fintype.card A * Fintype.card B := by
  rw [edgeFinset_completeBipartiteGraph, Finset.card_image_of_injective _ edgeMap_injective,
    Finset.card_univ, Fintype.card_prod]

private lemma graphonHomIntegrand_completeBipartiteGraph {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableRel (completeBipartiteGraph A B).Adj]
    (W : LimitObjects.Graphon) (z : A ⊕ B → UnitInterval) :
    graphonHomIntegrand (completeBipartiteGraph A B) W z =
      ∏ b : B, ∏ a : A, (W (z (Sum.inl a), z (Sum.inr b)) : ℝ) := by
  unfold graphonHomIntegrand
  rw [edgeFinset_completeBipartiteGraph, Finset.prod_image (fun _ _ _ _ h => edgeMap_injective h)]
  rw [Fintype.prod_prod_type_right]
  rfl

private lemma graphon_val_nonneg (W : LimitObjects.Graphon) (p : UnitInterval × UnitInterval) :
    0 ≤ (W p : ℝ) :=
  (W p).property.1

private lemma graphon_val_le_one (W : LimitObjects.Graphon) (p : UnitInterval × UnitInterval) :
    (W p : ℝ) ≤ 1 :=
  (W p).property.2

private lemma measurable_graphon_val (W : LimitObjects.Graphon) :
    Measurable (fun p : UnitInterval × UnitInterval => (W p : ℝ)) :=
  continuous_subtype_val.measurable.comp W.measurable

private lemma integrable_of_mem_unit {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hm : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    Integrable f μ :=
  Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    exact h1 x)

private lemma integral_le_one_of_le_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Integrable f μ) (h1 : ∀ x, f x ≤ 1) :
    ∫ x, f x ∂μ ≤ 1 := by
  calc ∫ x, f x ∂μ ≤ ∫ _ : α, (1 : ℝ) ∂μ := integral_mono hf (integrable_const 1) h1
    _ = 1 := by simp

private lemma integral_pow_ge_pow_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hm : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) (k : ℕ) :
    (∫ x, f x ∂μ) ^ k ≤ ∫ x, (f x) ^ k ∂μ :=
  (convexOn_pow k).map_integral_le (continuous_pow k).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall h0)
    (integrable_of_mem_unit hm h0 h1)
    (integrable_of_mem_unit (hm.pow_const k) (fun x => pow_nonneg (h0 x) k)
      (fun x => pow_le_one₀ (h0 x) (h1 x)))

theorem OMA.solution :
    type_of% @SidorenkoConjecture.sidorenko_completeBipartiteGraph_graphon := by
  intro A B _ _ _ _ W
  classical
  let μA : Measure (A → UnitInterval) := Measure.pi (fun _ => volume)
  let μB : Measure (B → UnitInterval) := Measure.pi (fun _ => volume)
  let μAB : Measure (A ⊕ B → UnitInterval) := Measure.pi (fun _ => volume)
  let F : (A → UnitInterval) → ℝ :=
    fun x => ∫ u : UnitInterval, (∏ a : A, (W (x a, u) : ℝ)) ∂volume
  let G : UnitInterval → ℝ :=
    fun u => ∫ v : UnitInterval, (W (v, u) : ℝ) ∂volume
  have hW_meas : Measurable (fun p : UnitInterval × UnitInterval => (W p : ℝ)) :=
    measurable_graphon_val W
  have hprodA_meas : Measurable (fun p : (A → UnitInterval) × UnitInterval =>
      ∏ a : A, (W (p.1 a, p.2) : ℝ)) :=
    Finset.measurable_prod Finset.univ fun a _ =>
      hW_meas.comp (((measurable_pi_apply a).comp measurable_fst).prodMk measurable_snd)
  have hprodA_nonneg : ∀ (x : A → UnitInterval) (u : UnitInterval),
      0 ≤ ∏ a : A, (W (x a, u) : ℝ) :=
    fun x u => Finset.prod_nonneg fun a _ => graphon_val_nonneg W (x a, u)
  have hprodA_le_one : ∀ (x : A → UnitInterval) (u : UnitInterval),
      ∏ a : A, (W (x a, u) : ℝ) ≤ 1 :=
    fun x u => Finset.prod_le_one (fun a _ => graphon_val_nonneg W (x a, u))
      (fun a _ => graphon_val_le_one W (x a, u))
  have hprodAB_meas : Measurable (fun p : (A → UnitInterval) × (B → UnitInterval) =>
      ∏ b : B, ∏ a : A, (W (p.1 a, p.2 b) : ℝ)) :=
    Finset.measurable_prod Finset.univ fun b _ =>
      Finset.measurable_prod Finset.univ fun a _ =>
        hW_meas.comp (((measurable_pi_apply a).comp measurable_fst).prodMk
          ((measurable_pi_apply b).comp measurable_snd))
  have hprodAB_int : Integrable (fun p : (A → UnitInterval) × (B → UnitInterval) =>
      ∏ b : B, ∏ a : A, (W (p.1 a, p.2 b) : ℝ)) (μA.prod μB) :=
    integrable_of_mem_unit hprodAB_meas
      (fun p => Finset.prod_nonneg fun b _ => hprodA_nonneg p.1 (p.2 b))
      (fun p => Finset.prod_le_one (fun b _ => hprodA_nonneg p.1 (p.2 b))
        (fun b _ => hprodA_le_one p.1 (p.2 b)))
  have hhom : graphonHomDensity (completeBipartiteGraph A B) W =
      ∫ x : A → UnitInterval, (F x) ^ Fintype.card B ∂μA := by
    unfold graphonHomDensity
    simp_rw [graphonHomIntegrand_completeBipartiteGraph]
    have hmp := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : A ⊕ B => UnitInterval)
      (fun _ => (volume : Measure UnitInterval))
    rw [← hmp.integral_comp']
    change (∫ p : (A → UnitInterval) × (B → UnitInterval),
      ∏ b : B, ∏ a : A, (W (p.1 a, p.2 b) : ℝ) ∂(μA.prod μB)) = _
    rw [MeasureTheory.integral_prod _ hprodAB_int]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact integral_fintype_prod_eq_pow (fun u : UnitInterval => ∏ a : A, (W (x a, u) : ℝ))
  have hF_meas : Measurable F := hprodA_meas.stronglyMeasurable.integral_prod_right'.measurable
  have hF_nonneg : ∀ x, 0 ≤ F x :=
    fun x => integral_nonneg fun u => hprodA_nonneg x u
  have hF_le_one : ∀ x, F x ≤ 1 := fun x =>
    integral_le_one_of_le_one
      (integrable_of_mem_unit
        (hprodA_meas.comp (measurable_const.prodMk measurable_id))
        (fun u => hprodA_nonneg x u)
        (fun u => hprodA_le_one x u))
      (fun u => hprodA_le_one x u)
  have hjensenB : (∫ x : A → UnitInterval, F x ∂μA) ^ Fintype.card B ≤
      ∫ x : A → UnitInterval, (F x) ^ Fintype.card B ∂μA :=
    integral_pow_ge_pow_integral hF_meas hF_nonneg hF_le_one (Fintype.card B)
  have hprodA_int : Integrable (fun p : (A → UnitInterval) × UnitInterval =>
      ∏ a : A, (W (p.1 a, p.2) : ℝ)) (μA.prod volume) :=
    integrable_of_mem_unit hprodA_meas
      (fun p => hprodA_nonneg p.1 p.2)
      (fun p => hprodA_le_one p.1 p.2)
  have hswap : ∫ x : A → UnitInterval, F x ∂μA =
      ∫ u : UnitInterval, (G u) ^ Fintype.card A ∂volume := by
    calc ∫ x : A → UnitInterval, F x ∂μA
        = ∫ u : UnitInterval,
            (∫ x : A → UnitInterval, (∏ a : A, (W (x a, u) : ℝ)) ∂μA) ∂volume :=
          MeasureTheory.integral_integral_swap hprodA_int
      _ = ∫ u : UnitInterval, (G u) ^ Fintype.card A ∂volume := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          exact integral_fintype_prod_eq_pow (fun v : UnitInterval => (W (v, u) : ℝ))
  have hG_meas : Measurable G := hW_meas.stronglyMeasurable.integral_prod_left'.measurable
  have hG_nonneg : ∀ u, 0 ≤ G u :=
    fun u => integral_nonneg fun v => graphon_val_nonneg W (v, u)
  have hG_le_one : ∀ u, G u ≤ 1 := fun u =>
    integral_le_one_of_le_one
      (integrable_of_mem_unit
        (hW_meas.comp (measurable_id.prodMk measurable_const))
        (fun v => graphon_val_nonneg W (v, u))
        (fun v => graphon_val_le_one W (v, u)))
      (fun v => graphon_val_le_one W (v, u))
  have hjensenA : (∫ u : UnitInterval, G u ∂volume) ^ Fintype.card A ≤
      ∫ u : UnitInterval, (G u) ^ Fintype.card A ∂volume :=
    integral_pow_ge_pow_integral hG_meas hG_nonneg hG_le_one (Fintype.card A)
  have hedge : ∫ u : UnitInterval, G u ∂volume = graphonEdgeDensity W := by
    unfold graphonEdgeDensity G
    have hW_int : Integrable (fun p : UnitInterval × UnitInterval => (W p : ℝ))
        (volume.prod volume) :=
      integrable_of_mem_unit hW_meas (graphon_val_nonneg W) (graphon_val_le_one W)
    exact (MeasureTheory.integral_prod_symm (fun p : UnitInterval × UnitInterval => (W p : ℝ))
      hW_int).symm
  have hedge_nonneg : 0 ≤ graphonEdgeDensity W :=
    integral_nonneg (graphon_val_nonneg W)
  rw [card_edgeFinset_completeBipartiteGraph, pow_mul, hhom]
  calc ((graphonEdgeDensity W) ^ Fintype.card A) ^ Fintype.card B
      ≤ (∫ x : A → UnitInterval, F x ∂μA) ^ Fintype.card B := by
        apply pow_le_pow_left₀ (pow_nonneg hedge_nonneg _)
        rw [hswap, ← hedge]
        exact hjensenA
    _ ≤ ∫ x : A → UnitInterval, (F x) ^ Fintype.card B ∂μA := hjensenB
