import FormalConjectures.HilbertProblems.«5»
import Mathlib.Algebra.Group.Shrink
import Mathlib.Logic.Small.Basic
import Mathlib.Logic.Small.Set
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Sequences

/-!
# Reduction of `Hilbert5.hilbert_smith_conjecture.variants.dimension_three` (Pardon 2013)

Reduces Pardon's theorem (the Hilbert–Smith conjecture for connected 3-manifolds) to three
independent, universe-monomorphic (`Type`) classical results:
1. `H1`: Gleason–Yamabe + Pontryagin duality dichotomy for non-Lie locally compact Hausdorff
   groups (either arbitrarily small nontrivial finite subgroups, or an embedded `ℤ_[p]`),
2. `H2`: Newman's theorem (1931) in the compact-open topology on `C(X, X)` (no nontrivial
   finite subgroup of homeomorphisms of a connected 3-manifold stays inside a small
   compact-open neighborhood of `id`),
3. `H3`: Pardon's 2013 obstruction to continuous faithful `ℤ_[p]`-actions on connected
   3-manifolds (`hilbert_smith_padic_formulation` in dimension 3).

References:
- J. Pardon, "The Hilbert–Smith conjecture for three-manifolds", J. Amer. Math. Soc. 26 (2013),
  879–899, arXiv:1112.2324.
- M. H. A. Newman, "A theorem on periodic transformations of spaces", Q. J. Math. 2 (1931), 1–8.
- T. Tao, "The Hilbert–Smith conjecture" (blog post, 2011).

Thanks to @MechaNuggan for the Hausdorffness, pullback, and `ℤ_[p]`-reduction outline.
Credit: @tkaiman
-/

noncomputable section

open scoped Manifold ContDiff Topology Ordinal Classical
open Set Filter

namespace OMA.R_Hilbert5_hilbert_smith_conjecture_variants_dimension_three_R1

/- ### Part 1: Universe descent (`Small.{0}`) for any connected Hausdorff `n`-manifold -/

private lemma firstCountable_of_chartedSpace {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] :
    FirstCountableTopology X := by
  refine ⟨fun x => ?_⟩
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hnhds : 𝓝 x = Filter.comap c (𝓝 (c x)) ⊓ 𝓟 c.source := by
    apply le_antisymm
    · exact le_inf
        (c.continuousAt (mem_chart_source _ x)).tendsto.le_comap
        (le_principal_iff.mpr (chart_source_mem_nhds _ x))
    · intro s hs
      have hsymm : ContinuousAt c.symm (c x) := c.continuousAt_symm (mem_chart_target _ x)
      have hpre : c.symm ⁻¹' s ∈ 𝓝 (c x) := by
        have hcx : c.symm (c x) = x := c.left_inv (mem_chart_source _ x)
        exact hsymm.preimage_mem_nhds (by rwa [hcx])
      refine Filter.mem_of_superset
        (Filter.inter_mem_inf (Filter.preimage_mem_comap hpre) (Filter.mem_principal_self c.source))
        ?_
      intro y ⟨hy1, hy2⟩
      have hinv : c.symm (c y) = y := c.left_inv hy2
      simpa [hinv] using hy1
  rw [hnhds]
  infer_instance

private lemma small_closure_of_firstCountable_t2 {X : Type*}
    [TopologicalSpace X] [T2Space X] [FirstCountableTopology X]
    {S : Set X} [Small.{0} S] : Small.{0} (closure S) := by
  have hex : ∀ y : closure S, ∃ u : ℕ → S, Tendsto (fun k => (u k : X)) atTop (𝓝 y.1) := by
    intro y
    obtain ⟨v, hvS, hvT⟩ := mem_closure_iff_seq_limit.mp y.2
    exact ⟨fun k => ⟨v k, hvS k⟩, hvT⟩
  choose f hf using hex
  have hf_inj : Function.Injective f := by
    intro y₁ y₂ hEq
    apply Subtype.ext
    exact tendsto_nhds_unique (hf y₁) (by rw [hEq]; exact hf y₂)
  exact small_of_injective hf_inj

private lemma small_of_connected_t2_manifold {n : ℕ} {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] : Small.{0} X := by
  have _ : FirstCountableTopology X := firstCountable_of_chartedSpace (n := n)
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  let step (α : Ordinal.{0}) (f : ∀ β < α, Set X) : Set X :=
    {x₀} ∪ closure (⋃ β : Set.Iio α, ⋃ x ∈ f β.1 β.2,
      (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
  let A : Ordinal.{0} → Set X := WellFoundedLT.fix step
  have hA_eq (α : Ordinal.{0}) :
      A α = {x₀} ∪ closure (⋃ β : Set.Iio α, ⋃ x ∈ A β.1,
        (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :=
    WellFoundedLT.fix_eq step α
  have hsrc_small (x : X) : Small.{0} (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    refine small_of_injective (f := fun y : c.source => c y.1) ?_
    intro y₁ y₂ hEq
    dsimp only at hEq
    apply Subtype.ext
    have h1 := c.left_inv y₁.2
    have h2 := c.left_inv y₂.2
    rw [← h1, ← h2, hEq]
  have hA_small : ∀ α : Ordinal.{0}, Small.{0} (A α) := by
    intro α
    induction α using WellFoundedLT.induction with
    | ind α ih =>
      rw [hA_eq α]
      have hinner : ∀ β : Set.Iio α,
          Small.{0} (⋃ x ∈ A β.1, (chartAt (EuclideanSpace ℝ (Fin n)) x).source) := by
        intro β
        have hβ : Small.{0} (A β.1) := ih β.1 β.2
        exact @small_biUnion.{0} _ _ (A β.1) hβ
          (fun x _ => (chartAt (EuclideanSpace ℝ (Fin n)) x).source) (fun x _ => hsrc_small x)
      have hunion : Small.{0} (⋃ β : Set.Iio α, ⋃ x ∈ A β.1,
          (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :=
        @small_iUnion.{0} _ _ (Ordinal.small_Iio α) _ hinner
      have hcl : Small.{0} (closure (⋃ β : Set.Iio α, ⋃ x ∈ A β.1,
          (chartAt (EuclideanSpace ℝ (Fin n)) x).source)) :=
        @small_closure_of_firstCountable_t2 _ _ _ _ _ hunion
      have hsing : Small.{0} ({x₀} : Set X) := inferInstance
      exact @small_union.{0} _ _ _ hsing hcl
  let U : Set X := ⋃ α : Set.Iio (ω₁ : Ordinal.{0}), A α.1
  have h0_lt : (0 : Ordinal.{0}) < ω₁ := (Cardinal.isSuccLimit_omega 1).bot_lt
  have hU_ne : U.Nonempty := by
    refine ⟨x₀, Set.mem_iUnion.mpr ⟨⟨0, h0_lt⟩, ?_⟩⟩
    rw [hA_eq 0]
    exact Or.inl rfl
  have hU_open : IsOpen U := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨⟨α, hα⟩, hxα⟩ := Set.mem_iUnion.mp hx
    have hsucc : Order.succ α < ω₁ := (Cardinal.isSuccLimit_omega 1).succ_lt hα
    refine ⟨(chartAt (EuclideanSpace ℝ (Fin n)) x).source, ?_,
      (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source, mem_chart_source _ x⟩
    intro y hy
    refine Set.mem_iUnion.mpr ⟨⟨Order.succ α, hsucc⟩, ?_⟩
    rw [hA_eq (Order.succ α)]
    refine Or.inr (subset_closure ?_)
    exact Set.mem_iUnion.mpr ⟨⟨α, Order.lt_succ α⟩, Set.mem_biUnion hxα hy⟩
  have hU_closed : IsClosed U := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    obtain ⟨u, huU, huT⟩ := mem_closure_iff_seq_limit.mp hy
    have hchoose : ∀ k : ℕ, ∃ α : Ordinal.{0}, α < ω₁ ∧ u k ∈ A α := by
      intro k
      obtain ⟨⟨α, hα⟩, hmem⟩ := Set.mem_iUnion.mp (huU k)
      exact ⟨α, hα, hmem⟩
    choose α hα_lt huα using hchoose
    let β : Ordinal.{0} := ⨆ k : ℕ, α k
    have hβ_lt : β < ω₁ := Ordinal.iSup_lt_omega_one hα_lt
    have hβ_bdd : BddAbove (Set.range α) := ⟨ω₁, by rintro _ ⟨k, rfl⟩; exact (hα_lt k).le⟩
    have hsucc : Order.succ β < ω₁ := (Cardinal.isSuccLimit_omega 1).succ_lt hβ_lt
    refine Set.mem_iUnion.mpr ⟨⟨Order.succ β, hsucc⟩, ?_⟩
    rw [hA_eq (Order.succ β)]
    refine Or.inr ?_
    refine mem_closure_iff_seq_limit.mpr ⟨u, fun k => ?_, huT⟩
    have hk_lt : α k < Order.succ β := Order.lt_succ_of_le (le_ciSup hβ_bdd k)
    exact Set.mem_iUnion.mpr
      ⟨⟨α k, hk_lt⟩, Set.mem_biUnion (huα k) (mem_chart_source _ (u k))⟩
  have hU_univ : U = Set.univ := IsClopen.eq_univ ⟨hU_closed, hU_open⟩ hU_ne
  have hU_small : Small.{0} U :=
    @small_iUnion.{0} _ _ (Ordinal.small_Iio (ω₁ : Ordinal.{0})) _ (fun α => hA_small α.1)
  rw [hU_univ] at hU_small
  exact small_of_surjective (f := fun x : (Set.univ : Set X) => x.1)
    (fun x => ⟨⟨x, Set.mem_univ x⟩, rfl⟩)

/- ### Part 2: Transporting charts and `AdmitsLieGroupStructure` along a homeomorphism -/

private abbrev homeomorphChartedSpace {H : Type*} [TopologicalSpace H]
    {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X'] [ChartedSpace H X]
    (e : X' ≃ₜ X) : ChartedSpace H X' where
  atlas := { c' | ∃ c ∈ atlas H X, c' = e.toOpenPartialHomeomorph.trans c }
  chartAt x' := e.toOpenPartialHomeomorph.trans (chartAt H (e x'))
  mem_chart_source x' := by simp
  chart_mem_atlas x' := ⟨chartAt H (e x'), chart_mem_atlas H (e x'), rfl⟩

private lemma homeomorphChartedSpace_isManifold {n : ℕ} {k : ℕ∞ω}
    {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) k X]
    (e : X' ≃ₜ X) :
    let _ := homeomorphChartedSpace (H := EuclideanSpace ℝ (Fin n)) e
    IsManifold (𝓡 n) k X' := by
  intro cs
  refine isManifold_of_contDiffOn (𝓡 n) k X' ?_
  intro c₁' c₂' hc₁' hc₂'
  rcases hc₁' with ⟨c₁, hc₁, rfl⟩
  rcases hc₂' with ⟨c₂, hc₂, rfl⟩
  have hmem := (contDiffGroupoid k (𝓡 n)).compatible hc₁ hc₂
  have hcd : ContDiffOn ℝ k ((c₁.symm.trans c₂) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (c₁.symm.trans c₂).source := by
    simpa [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm] using hmem.1
  have hsrc : ((e.toOpenPartialHomeomorph.trans c₁).symm.trans
      (e.toOpenPartialHomeomorph.trans c₂)).source = (c₁.symm.trans c₂).source := by
    ext y
    simp
  have hfun : ∀ y ∈ (c₁.symm.trans c₂).source,
      ((e.toOpenPartialHomeomorph.trans c₁).symm.trans
        (e.toOpenPartialHomeomorph.trans c₂)) y = (c₁.symm.trans c₂) y := by
    intro y _
    simp
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
  rw [hsrc]
  exact hcd.congr hfun

private lemma homeomorphChartedSpace_contMDiff_coe {n : ℕ} {k : ℕ∞ω}
    {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    (e : X' ≃ₜ X) :
    let _ := homeomorphChartedSpace (H := EuclideanSpace ℝ (Fin n)) e
    ContMDiff (𝓡 n) (𝓡 n) k e := by
  intro cs x'
  rw [contMDiffAt_iff]
  refine ⟨e.continuous.continuousAt, ?_⟩
  have hpt : extChartAt (𝓡 n) x' x' = chartAt (EuclideanSpace ℝ (Fin n)) (e x') (e x') := rfl
  have htarget : (chartAt (EuclideanSpace ℝ (Fin n)) (e x')).target ∈
      𝓝 (extChartAt (𝓡 n) x' x') := by
    rw [hpt]
    exact (chartAt (EuclideanSpace ℝ (Fin n)) (e x')).open_target.mem_nhds
      (mem_chart_target _ _)
  refine (contDiffWithinAt_id (𝕜 := ℝ) (n := k) (s := Set.range (𝓡 n))).congr_of_eventuallyEq
    ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds htarget] with y hy
    change (chartAt (EuclideanSpace ℝ (Fin n)) (e x'))
      (e (e.symm ((chartAt (EuclideanSpace ℝ (Fin n)) (e x')).symm y))) = y
    simp [(chartAt (EuclideanSpace ℝ (Fin n)) (e x')).right_inv hy]
  · change (chartAt (EuclideanSpace ℝ (Fin n)) (e x'))
      (e (e.symm ((chartAt (EuclideanSpace ℝ (Fin n)) (e x')).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) (e x')) (e x'))))) =
      (chartAt (EuclideanSpace ℝ (Fin n)) (e x')) (e x')
    simp [(chartAt (EuclideanSpace ℝ (Fin n)) (e x')).left_inv (mem_chart_source _ _)]

private lemma homeomorphChartedSpace_contMDiff_symm {n : ℕ} {k : ℕ∞ω}
    {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    (e : X' ≃ₜ X) :
    let _ := homeomorphChartedSpace (H := EuclideanSpace ℝ (Fin n)) e
    ContMDiff (𝓡 n) (𝓡 n) k e.symm := by
  intro cs x
  rw [contMDiffAt_iff]
  refine ⟨e.symm.continuous.continuousAt, ?_⟩
  have hpt : extChartAt (𝓡 n) x x = chartAt (EuclideanSpace ℝ (Fin n)) x x := rfl
  have htarget : (chartAt (EuclideanSpace ℝ (Fin n)) x).target ∈
      𝓝 (extChartAt (𝓡 n) x x) := by
    rw [hpt]
    exact (chartAt (EuclideanSpace ℝ (Fin n)) x).open_target.mem_nhds (mem_chart_target _ _)
  refine (contDiffWithinAt_id (𝕜 := ℝ) (n := k) (s := Set.range (𝓡 n))).congr_of_eventuallyEq
    ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds htarget] with y hy
    change (chartAt (EuclideanSpace ℝ (Fin n)) (e (e.symm x)))
      (e (e.symm ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm y))) = y
    simp [(chartAt (EuclideanSpace ℝ (Fin n)) x).right_inv hy]
  · change (chartAt (EuclideanSpace ℝ (Fin n)) (e (e.symm x)))
      (e (e.symm ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) x) x)))) =
      (chartAt (EuclideanSpace ℝ (Fin n)) x) x
    simp [(chartAt (EuclideanSpace ℝ (Fin n)) x).left_inv (mem_chart_source _ _)]

private lemma admitsLieGroupStructure_of_continuousMulEquiv
    {G : Type*} [Group G] [TopologicalSpace G]
    {G' : Type*} [Group G'] [TopologicalSpace G']
    (φ : G' ≃ₜ* G) (hG' : AdmitsLieGroupStructure G') :
    AdmitsLieGroupStructure G := by
  obtain ⟨m, ⟨p⟩⟩ := hG'
  let L := p.carrier
  let _ : TopologicalSpace L := p.topologicalSpace
  let _ : Group L := p.group
  have _ : T2Space L := p.t2Space
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) L := p.chartedSpace
  have _ : IsManifold (𝓡 m) ω L := p.isManifold
  have _ : LieGroup (𝓡 m) ω L := p.lieGroup
  let ψ : G ≃ₜ* L := φ.symm.trans p.equiv
  have _ : T2Space G := ψ.toHomeomorph.isEmbedding.t2Space
  let csG : ChartedSpace (EuclideanSpace ℝ (Fin m)) G :=
    homeomorphChartedSpace ψ.toHomeomorph
  have hManG : IsManifold (𝓡 m) ω G := homeomorphChartedSpace_isManifold ψ.toHomeomorph
  have hψ : ContMDiff (𝓡 m) (𝓡 m) ω ψ :=
    homeomorphChartedSpace_contMDiff_coe ψ.toHomeomorph
  have hψs : ContMDiff (𝓡 m) (𝓡 m) ω ψ.symm :=
    homeomorphChartedSpace_contMDiff_symm ψ.toHomeomorph
  have hmul : ContMDiff ((𝓡 m).prod (𝓡 m)) (𝓡 m) ω (fun q : G × G => q.1 * q.2) := by
    have heq : (fun q : G × G => q.1 * q.2) =
        (ψ.symm ∘ (fun q : L × L => q.1 * q.2) ∘ Prod.map ψ ψ) := by
      funext ⟨a, b⟩; simp [Prod.map]
    rw [heq]
    exact hψs.comp ((contMDiff_mul (I := 𝓡 m) (n := ω)).comp (hψ.prodMap hψ))
  have hinv : ContMDiff (𝓡 m) (𝓡 m) ω (fun a : G => a⁻¹) := by
    have heq : (fun a : G => a⁻¹) = (ψ.symm ∘ (fun z : L => z⁻¹) ∘ ψ) := by
      funext a; simp
    rw [heq]
    exact hψs.comp ((contMDiff_inv (𝓡 m) ω).comp hψ)
  have hLieG : LieGroup (𝓡 m) ω G :=
    { contMDiff_mul := hmul
      contMDiff_inv := hinv }
  exact ⟨m, ⟨{
    carrier := G
    topologicalSpace := inferInstance
    group := inferInstance
    t2Space := inferInstance
    chartedSpace := csG
    isManifold := hManG
    lieGroup := hLieG
    equiv := ContinuousMulEquiv.refl G
  }⟩⟩

/- ### Part 3: Hypotheses and main reduction theorem -/

/-- **Gleason–Yamabe + Pontryagin duality dichotomy (in `Type`)**:
every locally compact Hausdorff topological group that does not admit a Lie group structure
either has nontrivial finite subgroups inside every open neighborhood of `1`, or admits a
continuous injective homomorphism from the additive `p`-adic integers `ℤ_[p]` for some prime `p`. -/
def H1 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G],
    ¬ AdmitsLieGroupStructure G →
      (∀ V : Set G, IsOpen V → (1 : G) ∈ V →
        ∃ F : Subgroup G, F ≠ ⊥ ∧ Finite F ∧ (F : Set G) ⊆ V) ∨
      (∃ (p : ℕ) (_ : Fact p.Prime) (f : ℤ_[p] → G),
        (∀ a b, f (a + b) = f a * f b) ∧ Continuous f ∧ Function.Injective f)

/-- **Newman's theorem on periodic homeomorphisms of 3-manifolds (in `Type`)**:
for every connected Hausdorff topological 3-manifold `X`, there exists a compact-open
neighborhood `U` of `id` in `C(X, X)` that contains no nontrivial finite subgroup of
homeomorphisms of `X`. -/
def H2 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X],
    ∃ U : Set C(X, X), IsOpen U ∧ ContinuousMap.id X ∈ U ∧
      ∀ F : Subgroup (Equiv.Perm X), Finite F →
        (∀ e ∈ F, ∃ c : C(X, X), (c : X → X) = e ∧ c ∈ U) → F = ⊥

/-- **Pardon's theorem (2013) in `p`-adic form (in `Type`)**:
the `p`-adic integers `ℤ_[p]` cannot act continuously and faithfully on a connected Hausdorff
topological 3-manifold. -/
def H3 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (p : ℕ) [Fact p.Prime] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X],
    ¬ FaithfulVAdd ℤ_[p] X

theorem main : H1 → H2 → H3 →
    type_of% @Hilbert5.hilbert_smith_conjecture.variants.dimension_three := by
  intro h1 h2 h3 G _ _ X hTopX hT2X hConnX hCSX hTG hLC hAct hCSmul hFaith
  -- Step 1: Universe descent Small.{0} X and Small.{0} G
  have hSmallX : Small.{0} X := small_of_connected_t2_manifold (n := 3)
  let actX (g : G) (x : X) : X := g • x
  have hactX_inj : Function.Injective actX := fun _ _ h => eq_of_smul_eq_smul (congrFun h)
  have hSmallG : Small.{0} G := small_of_injective hactX_inj
  -- Step 2: Transport X to X' := Shrink.{0} X : Type
  let X' : Type := Shrink.{0} X
  let e : X' ≃ X := (equivShrink X).symm
  let _ : TopologicalSpace X' := TopologicalSpace.induced e inferInstance
  let e_hom : X' ≃ₜ X :=
    { toEquiv := e
      continuous_toFun := continuous_induced_dom
      continuous_invFun := continuous_induced_rng.mpr (by
        convert continuous_id; funext x; exact e.apply_symm_apply x) }
  have hT2X' : T2Space X' := e_hom.isEmbedding.t2Space
  have hConnX' : ConnectedSpace X' :=
    connectedSpace_iff_univ.mpr <| by
      simpa [Set.image_univ, e_hom.symm.range_coe] using
        isConnected_univ.image e_hom.symm e_hom.symm.continuous.continuousOn
  let csX' : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X' := homeomorphChartedSpace e_hom
  -- Step 3: Transport G to G' := Shrink.{0} G : Type with faithful continuous action on X'
  let G' : Type := Shrink.{0} G
  let φ_mul : G' ≃* G := Shrink.mulEquiv
  let _ : TopologicalSpace G' := TopologicalSpace.induced φ_mul inferInstance
  let φ : G' ≃ₜ* G :=
    { toMulEquiv := φ_mul
      continuous_toFun := continuous_induced_dom
      continuous_invFun := continuous_induced_rng.mpr (by
        convert continuous_id; funext g; exact φ_mul.apply_symm_apply g) }
  have hTG' : IsTopologicalGroup G' :=
    { continuous_mul := by
        have heq : (fun p : G' × G' => p.1 * p.2) =
            (φ.symm ∘ (fun q : G × G => q.1 * q.2) ∘ Prod.map φ φ) := by
          funext ⟨a, b⟩; simp [Prod.map]
        rw [heq]
        exact φ.symm.continuous.comp (continuous_mul.comp (φ.continuous.prodMap φ.continuous))
      continuous_inv := by
        have heq : (fun a : G' => a⁻¹) = (φ.symm ∘ (fun g : G => g⁻¹) ∘ φ) := by
          funext a; simp
        rw [heq]
        exact φ.symm.continuous.comp (continuous_inv.comp φ.continuous) }
  have hLC' : LocallyCompactSpace G' := φ.toHomeomorph.locallyCompactSpace_iff.mpr hLC
  let instAct' : MulAction G' X' :=
    { smul := fun g' x' => e.symm ((φ g') • (e x'))
      one_smul := fun x' => by show e.symm ((φ 1) • e x') = x'; simp
      mul_smul := fun g₁' g₂' x' => by
        show e.symm ((φ (g₁' * g₂')) • e x') = e.symm ((φ g₁') • e (e.symm ((φ g₂') • e x')))
        simp [map_mul, mul_smul] }
  have hCSmul' : ContinuousSMul G' X' :=
    ⟨e_hom.symm.continuous.comp
      (continuous_smul.comp ((φ.continuous.comp continuous_fst).prodMk
        (e_hom.continuous.comp continuous_snd)))⟩
  have hFaith' : FaithfulSMul G' X' :=
    ⟨fun {g₁ g₂} h => φ.injective (eq_of_smul_eq_smul fun x => by
      have hx := congrArg e (h (e.symm x))
      change e (e.symm ((φ g₁) • e (e.symm x))) = e (e.symm ((φ g₂) • e (e.symm x))) at hx
      simpa using hx)⟩
  -- Step 4: Hausdorffness of G' via pointwise orbit evaluation
  let evalAct (g' : G') (x' : X') : X' := g' • x'
  have heval_cont : Continuous evalAct := continuous_pi fun x' => continuous_id.smul continuous_const
  have heval_inj : Function.Injective evalAct := fun _ _ h => eq_of_smul_eq_smul (congrFun h)
  have hT2G' : T2Space G' := T2Space.of_injective_continuous heval_inj heval_cont
  -- Step 5: Prove AdmitsLieGroupStructure G' by contradiction using H1, H2, H3
  have hLieG' : AdmitsLieGroupStructure G' := by
    by_contra hnotLie
    rcases h1 G' hnotLie with hfin_small | ⟨p, hp, f, hfmul, hfcont, hfinj⟩
    · -- Case 1: Arbitrarily small nontrivial finite subgroups contradict Newman's theorem (H2)
      obtain ⟨U, hU_open, hidU, hU_newman⟩ := h2 X'
      let actC : G' → C(X', X') := fun g' =>
        ⟨fun x' => g' • x', continuous_const_smul g'⟩
      have hactC_cont : Continuous actC :=
        ContinuousMap.continuous_of_continuous_uncurry actC continuous_smul
      have h1U : actC 1 ∈ U := by
        have h1eq : actC 1 = ContinuousMap.id X' := by
          apply ContinuousMap.ext; intro x'; exact one_smul G' x'
        rwa [h1eq]
      obtain ⟨F, hF_ne, hF_fin, hF_sub⟩ := hfin_small (actC ⁻¹' U) (hU_open.preimage hactC_cont) h1U
      let ρ : G' →* Equiv.Perm X' := MulAction.toPermHom G' X'
      have hmap_fin : Finite (F.map ρ) := Set.Finite.to_subtype ((Set.toFinite (F : Set G')).image ρ)
      have hmap_bot : F.map ρ = ⊥ := by
        apply hU_newman (F.map ρ) hmap_fin
        rintro _ ⟨g', hg', rfl⟩
        exact ⟨actC g', rfl, hF_sub hg'⟩
      apply hF_ne
      apply le_antisymm _ bot_le
      intro g' hg'
      have hmem : ρ g' ∈ F.map ρ := ⟨g', hg', rfl⟩
      rw [hmap_bot] at hmem
      have heq : ρ g' = 1 := Subgroup.mem_bot.mp hmem
      apply MulAction.toPerm_injective (β := X')
      change ρ g' = ρ 1
      simpa only [map_one] using heq
    · -- Case 2: Embedded ℤ_[p] acts continuously and faithfully on X', contradicting Pardon (H3)
      have hf0 : f 0 = 1 := by
        have h00 := hfmul 0 0
        rw [add_zero] at h00
        exact mul_left_cancel (a := f 0) (by simpa using h00.symm)
      let instVAdd : AddAction ℤ_[p] X' :=
        { vadd := fun z x' => f z • x'
          zero_vadd := fun x' => by show f 0 • x' = x'; rw [hf0, one_smul]
          add_vadd := fun z₁ z₂ x' => by
            show f (z₁ + z₂) • x' = f z₁ • (f z₂ • x')
            rw [hfmul, mul_smul] }
      have hCVAdd : ContinuousVAdd ℤ_[p] X' :=
        ⟨continuous_smul.comp ((hfcont.comp continuous_fst).prodMk continuous_snd)⟩
      have hFVAdd : FaithfulVAdd ℤ_[p] X' :=
        ⟨fun {z₁ z₂} h => hfinj (eq_of_smul_eq_smul h)⟩
      exact h3 X' p hFVAdd
  -- Step 6: Lift AdmitsLieGroupStructure G' back to G : Type u
  exact admitsLieGroupStructure_of_continuousMulEquiv φ hLieG'

end OMA.R_Hilbert5_hilbert_smith_conjecture_variants_dimension_three_R1
