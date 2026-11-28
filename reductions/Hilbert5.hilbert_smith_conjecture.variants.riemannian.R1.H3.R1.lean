import OMAReductions.R_Hilbert5_hilbert_smith_conjecture_variants_riemannian_R1
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Connected.Clopen

/-!
# Reduction of `Hilbert5.hilbert_smith_conjecture.variants.riemannian.R1.H3`

Following A. M. Gleason (1952), D. Montgomery & L. Zippin (1952), H. Yamabe (1953), and É. Cartan,
we reduce the locally compact Hausdorff No-Small-Subgroups theorem (`NSS ⇒ AdmitsLieGroupStructure`)
in `Type` to two canonical, independent pillars:

1. `H1`: **Gleason–Yamabe approximation theorem** (Yamabe 1953): every locally compact Hausdorff
   topological group `G : Type` has an open subgroup `G' ≤ G` such that every open neighborhood
   `V` of `1` in `G` contains a compact normal subgroup `K ◁ G'` (`((↑) : G' → G) '' K ⊆ V`)
   whose quotient `G' ⧸ K` admits a Lie group structure.
2. `H2`: **Cartan's automatic analyticity**: every continuous endomorphism `α : L →* L` of a
   finite-dimensional real-analytic Lie group `L : Type` is real-analytic (`ContMDiff (𝓡 n) (𝓡 n) ω`).

Inside `main`, we prove completely from scratch:
- **Open-subgroup Lie globalization**: if an open subgroup `G' ≤ G` admits a real-analytic Lie
  group structure, then the identity component `G₀ = connectedComponentOfOne G` is an open normal
  subgroup of `G` contained in `G'`, inherits a real-analytic Lie group structure `L₀` by
  restricting the charts of `G'`'s Lie presentation, and left-translating the analytic atlas of
  `L₀` across cosets of `G₀` (with `H2` for conjugation automorphisms) equips all of `G` with a
  real-analytic Lie group structure (`AdmitsLieGroupStructure G`).
- **NSS kills the Yamabe kernel**: pushing `K ◁ G'` into `G` gives a subgroup `K.map G'.subtype`
  contained in the NSS neighborhood `V`, forcing `K = ⊥`, hence `G' ≃ₜ* G' ⧸ K` admits a Lie group
  structure, and open-subgroup globalization concludes `AdmitsLieGroupStructure G`.

Credit: @tkaiman
-/

noncomputable section

open Set Topology Filter TopologicalSpace
open scoped Manifold ContDiff Pointwise Classical

namespace OMA.R_Hilbert5_hilbert_smith_conjecture_variants_riemannian_R1_H3_R1

/- ### Part 1: Identity component of a locally Euclidean group and open-subgroup chart restriction -/

private lemma isOpen_connectedComponent_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) G] :
    IsOpen (connectedComponent (1 : G)) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hmem_t : e x ∈ e.target := e.map_source (mem_chart_source _ x)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) hmem_t
  let U : Set G := e.source ∩ e ⁻¹' Metric.ball (e x) r
  have hU_open : IsOpen U :=
    e.continuousOn_toFun.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  have hxU : x ∈ U := ⟨mem_chart_source _ x, Metric.mem_ball_self hr⟩
  have hU_eq : U = e.symm '' Metric.ball (e x) r := by
    ext y
    constructor
    · rintro ⟨hy_s, hy_b⟩
      exact ⟨e y, hy_b, e.left_inv hy_s⟩
    · rintro ⟨z, hz_b, rfl⟩
      have hz_t : z ∈ e.target := hball hz_b
      exact ⟨e.map_target hz_t, by
        show e (e.symm z) ∈ Metric.ball (e x) r; rw [e.right_inv hz_t]; exact hz_b⟩
  have hU_conn : IsConnected U := by
    rw [hU_eq]
    have hb_conn : IsConnected (Metric.ball (e x) r) :=
      (convex_ball (e x) r).isConnected (Metric.nonempty_ball.mpr hr)
    exact hb_conn.image e.symm (e.continuousOn_invFun.mono hball)
  have hU_sub : U ⊆ connectedComponent (1 : G) := by
    have h1 : U ⊆ connectedComponent x :=
      hU_conn.isPreconnected.subset_connectedComponent hxU
    have h2 : connectedComponent x = connectedComponent (1 : G) :=
      (connectedComponent_eq hx).symm
    rwa [← h2]
  exact Filter.mem_of_superset (hU_open.mem_nhds hxU) hU_sub

private lemma connectedComponentOfOne_normal {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    (Subgroup.connectedComponentOfOne G).Normal where
  conj_mem a ha g := by
    have hcont : Continuous (fun x : G => g * x * g⁻¹) :=
      (continuous_const.mul continuous_id).mul continuous_const
    have himg := hcont.image_connectedComponent_subset (1 : G)
    simp only [mul_one, mul_inv_cancel] at himg
    exact himg ⟨a, ha, rfl⟩

private lemma connectedComponentOfOne_le_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (G' : Subgroup G) (hG'_open : IsOpen (G' : Set G)) :
    Subgroup.connectedComponentOfOne G ≤ G' := by
  let G₀ := Subgroup.connectedComponentOfOne G
  have : ConnectedSpace G₀ := Subtype.connectedSpace isConnected_connectedComponent
  have hcl : IsClosed (G' : Set G) := Subgroup.isClosed_of_isOpen G' hG'_open
  have hclopen : IsClopen (((↑) : G₀ → G) ⁻¹' (G' : Set G)) :=
    ⟨hcl.preimage continuous_subtype_val, hG'_open.preimage continuous_subtype_val⟩
  have huniv : ((↑) : G₀ → G) ⁻¹' (G' : Set G) = Set.univ :=
    hclopen.eq_univ ⟨1, G'.one_mem⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : G₀) ∈ ((↑) : G₀ → G) ⁻¹' (G' : Set G) := by rw [huniv]; trivial
  exact hmem

private lemma connectedComponentOfOne_eq_image_openSubgroup {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (G' : Subgroup G) (hG'_open : IsOpen (G' : Set G)) :
    (Subgroup.connectedComponentOfOne G : Set G) =
      ((↑) : G' → G) '' (Subgroup.connectedComponentOfOne G' : Set G') := by
  have hle := connectedComponentOfOne_le_of_isOpen G' hG'_open
  ext x
  constructor
  · intro hx
    have hx' : x ∈ G' := hle hx
    refine ⟨⟨x, hx'⟩, ?_, rfl⟩
    let S : Set G' := ((↑) : G' → G) ⁻¹' (Subgroup.connectedComponentOfOne G : Set G)
    have hS_img : ((↑) : G' → G) '' S = (Subgroup.connectedComponentOfOne G : Set G) := by
      ext y
      constructor
      · rintro ⟨⟨z, _⟩, hz, rfl⟩; exact hz
      · intro hy; exact ⟨⟨y, hle hy⟩, hy, rfl⟩
    have hS_conn : IsPreconnected S := by
      rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
      change IsPreconnected (((↑) : G' → G) '' S)
      rw [hS_img]
      exact isPreconnected_connectedComponent
    have h1S : (1 : G') ∈ S := mem_connectedComponent
    exact hS_conn.subset_connectedComponent h1S hx
  · rintro ⟨y, hy, rfl⟩
    have himg := continuous_subtype_val.image_connectedComponent_subset (1 : G')
    exact himg ⟨y, hy, rfl⟩

/- ### Part 2: Restricting a real-analytic Lie group to an open subgroup -/

private abbrev openSubgroupChartedSpace {L : Type*} [Group L] [TopologicalSpace L]
    {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) L]
    (U : Subgroup L) (hU : IsOpen (U : Set L)) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) U :=
  let inc : OpenPartialHomeomorph U L :=
    hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph ((↑) : U → L)
  { atlas := { inc.trans e | e ∈ atlas (EuclideanSpace ℝ (Fin n)) L }
    chartAt := fun x => inc.trans (chartAt (EuclideanSpace ℝ (Fin n)) (x : L))
    mem_chart_source := fun x => ⟨trivial, mem_chart_source _ (x : L)⟩
    chart_mem_atlas := fun x => ⟨chartAt (EuclideanSpace ℝ (Fin n)) (x : L), chart_mem_atlas _ _, rfl⟩ }

private lemma openSubgroup_isManifold {L : Type*} [Group L] [TopologicalSpace L]
    {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) L] [IsManifold (𝓡 n) ω L]
    (U : Subgroup L) (hU : IsOpen (U : Set L)) :
    let _ := openSubgroupChartedSpace (n := n) U hU
    IsManifold (𝓡 n) ω U := by
  intro csU
  let inc : OpenPartialHomeomorph U L :=
    hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph ((↑) : U → L)
  refine isManifold_of_contDiffOn (𝓡 n) ω U fun e₁ e₂ he₁ he₂ => ?_
  rcases he₁ with ⟨c₁, hc₁, rfl⟩
  rcases he₂ with ⟨c₂, hc₂, rfl⟩
  have hmem := (contDiffGroupoid ω (𝓡 n)).compatible hc₁ hc₂
  have hcd : ContDiffOn ℝ ω ((c₁.symm.trans c₂) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (c₁.symm.trans c₂).source := by
    simpa [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm] using hmem.1
  have hsub : ((inc.trans c₁).symm ≫ₕ (inc.trans c₂)).source ⊆ (c₁.symm.trans c₂).source := by
    intro y hy
    have hy1 : y ∈ c₁.target := hy.1.1
    have h2 : inc.symm (c₁.symm y) ∈ (inc.trans c₂).source := hy.2
    have hc2 : c₁.symm y ∈ c₂.source := by
      have : inc (inc.symm (c₁.symm y)) ∈ c₂.source := h2.2
      rwa [inc.right_inv hy.1.2] at this
    exact ⟨hy1, hc2⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
  refine (hcd.mono hsub).congr fun y hy => ?_
  change c₂ (inc (inc.symm (c₁.symm y))) = c₂ (c₁.symm y)
  rw [inc.right_inv hy.1.2]

private lemma openSubgroup_lieGroup {L : Type*} [Group L] [TopologicalSpace L]
    {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) L]
    [LieGroup (𝓡 n) ω L] (U : Subgroup L) (hU : IsOpen (U : Set L)) :
    let _ := openSubgroupChartedSpace (n := n) U hU
    let _ := openSubgroup_isManifold (n := n) U hU
    LieGroup (𝓡 n) ω U := by
  intro csU hManU
  let inc : OpenPartialHomeomorph U L :=
    hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph ((↑) : U → L)
  have hTG : IsTopologicalGroup L :=
    { continuous_mul := (contMDiff_mul (I := 𝓡 n) (n := ω) (G := L)).continuous
      continuous_inv := (contMDiff_inv (𝓡 n) ω (G := L)).continuous }
  have hmul : ContMDiff ((𝓡 n).prod (𝓡 n)) (𝓡 n) ω (fun p : U × U => p.1 * p.2) := by
    intro ⟨u₁, u₂⟩
    rw [contMDiffAt_iff]
    refine ⟨continuous_mul.continuousAt, ?_⟩
    have hL_at := (contMDiffAt_iff.mp ((contMDiff_mul (I := 𝓡 n) (n := ω) (G := L)) ((u₁ : L), (u₂ : L)))).2
    let c₁ := chartAt (EuclideanSpace ℝ (Fin n)) (u₁ : L)
    let c₂ := chartAt (EuclideanSpace ℝ (Fin n)) (u₂ : L)
    let c₁₂ := chartAt (EuclideanSpace ℝ (Fin n)) ((u₁ * u₂ : U) : L)
    have hpt : extChartAt ((𝓡 n).prod (𝓡 n)) (u₁, u₂) (u₁, u₂) =
        extChartAt ((𝓡 n).prod (𝓡 n)) ((u₁ : L), (u₂ : L)) ((u₁ : L), (u₂ : L)) := rfl
    rw [hpt]
    have hnhds1 : c₁.target ∩ c₁.symm ⁻¹' (U : Set L) ∈ 𝓝 (c₁ (u₁ : L)) := by
      have hopen : IsOpen (c₁.target ∩ c₁.symm ⁻¹' (U : Set L)) :=
        c₁.continuousOn_invFun.isOpen_inter_preimage c₁.open_target hU
      refine hopen.mem_nhds ⟨c₁.map_source (mem_chart_source _ (u₁ : L)), ?_⟩
      rw [Set.mem_preimage, c₁.left_inv (mem_chart_source _ (u₁ : L))]
      exact u₁.2
    have hnhds2 : c₂.target ∩ c₂.symm ⁻¹' (U : Set L) ∈ 𝓝 (c₂ (u₂ : L)) := by
      have hopen : IsOpen (c₂.target ∩ c₂.symm ⁻¹' (U : Set L)) :=
        c₂.continuousOn_invFun.isOpen_inter_preimage c₂.open_target hU
      refine hopen.mem_nhds ⟨c₂.map_source (mem_chart_source _ (u₂ : L)), ?_⟩
      rw [Set.mem_preimage, c₂.left_inv (mem_chart_source _ (u₂ : L))]
      exact u₂.2
    have hprod_nhds : (c₁.target ∩ c₁.symm ⁻¹' (U : Set L)) ×ˢ
        (c₂.target ∩ c₂.symm ⁻¹' (U : Set L)) ∈
        𝓝 (extChartAt ((𝓡 n).prod (𝓡 n)) ((u₁ : L), (u₂ : L)) ((u₁ : L), (u₂ : L))) := by
      change (c₁.target ∩ c₁.symm ⁻¹' (U : Set L)) ×ˢ (c₂.target ∩ c₂.symm ⁻¹' (U : Set L)) ∈
        𝓝 (c₁ (u₁ : L), c₂ (u₂ : L))
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod hnhds1 hnhds2
    refine hL_at.congr_of_eventuallyEq (Filter.mem_of_superset (nhdsWithin_le_nhds hprod_nhds) ?_) ?_
    · rintro ⟨y₁, y₂⟩ ⟨⟨_, hy₁U⟩, ⟨_, hy₂U⟩⟩
      have h1 : (inc.symm (c₁.symm y₁) : L) = c₁.symm y₁ :=
        inc.right_inv (by simpa [inc, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using hy₁U)
      have h2 : (inc.symm (c₂.symm y₂) : L) = c₂.symm y₂ :=
        inc.right_inv (by simpa [inc, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using hy₂U)
      change c₁₂ ((inc.symm (c₁.symm y₁) : L) * (inc.symm (c₂.symm y₂) : L)) =
        c₁₂ (c₁.symm y₁ * c₂.symm y₂)
      rw [h1, h2]
    · have h1 : (inc.symm (c₁.symm (c₁ (u₁ : L))) : L) = c₁.symm (c₁ (u₁ : L)) := by
        rw [c₁.left_inv (mem_chart_source _ (u₁ : L))]
        exact inc.right_inv (by simp [inc, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target])
      have h2 : (inc.symm (c₂.symm (c₂ (u₂ : L))) : L) = c₂.symm (c₂ (u₂ : L)) := by
        rw [c₂.left_inv (mem_chart_source _ (u₂ : L))]
        exact inc.right_inv (by simp [inc, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target])
      change c₁₂ ((inc.symm (c₁.symm (c₁ (u₁ : L))) : L) * (inc.symm (c₂.symm (c₂ (u₂ : L))) : L)) =
        c₁₂ (c₁.symm (c₁ (u₁ : L)) * c₂.symm (c₂ (u₂ : L)))
      rw [h1, h2]
  have hinv : ContMDiff (𝓡 n) (𝓡 n) ω (fun u : U => u⁻¹) := by
    intro u
    rw [contMDiffAt_iff]
    refine ⟨continuous_inv.continuousAt, ?_⟩
    have hL_at := (contMDiffAt_iff.mp ((contMDiff_inv (𝓡 n) ω (G := L)) (u : L))).2
    let c := chartAt (EuclideanSpace ℝ (Fin n)) (u : L)
    let ci := chartAt (EuclideanSpace ℝ (Fin n)) ((u⁻¹ : U) : L)
    have hpt : extChartAt (𝓡 n) u u = extChartAt (𝓡 n) (u : L) (u : L) := rfl
    rw [hpt]
    have hnhds : c.target ∩ c.symm ⁻¹' (U : Set L) ∈ 𝓝 (extChartAt (𝓡 n) (u : L) (u : L)) := by
      change c.target ∩ c.symm ⁻¹' (U : Set L) ∈ 𝓝 (c (u : L))
      have hopen : IsOpen (c.target ∩ c.symm ⁻¹' (U : Set L)) :=
        c.continuousOn_invFun.isOpen_inter_preimage c.open_target hU
      refine hopen.mem_nhds ⟨c.map_source (mem_chart_source _ (u : L)), ?_⟩
      rw [Set.mem_preimage, c.left_inv (mem_chart_source _ (u : L))]
      exact u.2
    refine hL_at.congr_of_eventuallyEq (Filter.mem_of_superset (nhdsWithin_le_nhds hnhds) ?_) ?_
    · rintro y ⟨_, hyU⟩
      have h1 : (inc.symm (c.symm y) : L) = c.symm y :=
        inc.right_inv (by simpa [inc, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using hyU)
      change ci ((inc.symm (c.symm y) : L)⁻¹) = ci ((c.symm y)⁻¹)
      rw [h1]
    · have h1 : (inc.symm (c.symm (c (u : L))) : L) = c.symm (c (u : L)) := by
        rw [c.left_inv (mem_chart_source _ (u : L))]
        exact inc.right_inv (by simp [inc, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target])
      change ci ((inc.symm (c.symm (c (u : L))) : L)⁻¹) = ci ((c.symm (c (u : L)))⁻¹)
      rw [h1]
  exact { contMDiff_mul := hmul, contMDiff_inv := hinv }

/- ### Part 3: Coset-translated analytic Lie atlas from `G₀` to `G` -/

private def cosetPartialHomeo {G L : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    (hG₀_open : IsOpen ((Subgroup.connectedComponentOfOne G : Set G)))
    (ψ : Subgroup.connectedComponentOfOne G ≃ₜ* L) (g : G) :
    OpenPartialHomeomorph G L where
  toFun x := if hx : g⁻¹ * x ∈ Subgroup.connectedComponentOfOne G then ψ ⟨g⁻¹ * x, hx⟩ else 1
  invFun y := g * (ψ.symm y : G)
  source := (fun x : G => g⁻¹ * x) ⁻¹' (Subgroup.connectedComponentOfOne G : Set G)
  target := Set.univ
  map_source' _ _ := trivial
  map_target' y _ := by
    show g⁻¹ * (g * (ψ.symm y : G)) ∈ Subgroup.connectedComponentOfOne G
    rw [inv_mul_cancel_left]
    exact (ψ.symm y).2
  left_inv' x hx := by
    have hx' : g⁻¹ * x ∈ Subgroup.connectedComponentOfOne G := hx
    simp only [dif_pos hx', ContinuousMulEquiv.symm_apply_apply]
    exact mul_inv_cancel_left g x
  right_inv' y _ := by
    have hm : g⁻¹ * (g * (ψ.symm y : G)) ∈ Subgroup.connectedComponentOfOne G := by
      rw [inv_mul_cancel_left]; exact (ψ.symm y).2
    rw [dif_pos hm]
    have hsub : (⟨g⁻¹ * (g * (ψ.symm y : G)), hm⟩ : Subgroup.connectedComponentOfOne G) = ψ.symm y :=
      Subtype.ext (inv_mul_cancel_left g (ψ.symm y : G))
    rw [hsub, ContinuousMulEquiv.apply_symm_apply]
  open_source := hG₀_open.preimage (continuous_const.mul continuous_id)
  open_target := isOpen_univ
  continuousOn_toFun := by
    let φ : ((fun x : G => g⁻¹ * x) ⁻¹' (Subgroup.connectedComponentOfOne G : Set G)) → L :=
      fun x => ψ ⟨g⁻¹ * x.1, x.2⟩
    have hφ_cont : Continuous φ := by
      refine ψ.continuous.comp (Continuous.subtype_mk ?_ _)
      exact continuous_const.mul continuous_subtype_val
    rw [continuousOn_iff_continuous_domRestrict]
    refine hφ_cont.congr fun x => ?_
    have hx : g⁻¹ * x.1 ∈ Subgroup.connectedComponentOfOne G := x.2
    change ψ ⟨g⁻¹ * x.1, hx⟩ =
      if h : g⁻¹ * x.1 ∈ Subgroup.connectedComponentOfOne G then ψ ⟨g⁻¹ * x.1, h⟩ else 1
    rw [dif_pos hx]
  continuousOn_invFun :=
    (continuous_const.mul (continuous_subtype_val.comp ψ.symm.continuous)).continuousOn

private abbrev cosetChartedSpace {G L : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) L]
    (hG₀_open : IsOpen ((Subgroup.connectedComponentOfOne G : Set G)))
    (ψ : Subgroup.connectedComponentOfOne G ≃ₜ* L) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) G where
  atlas := { e | ∃ (g : G) (c : OpenPartialHomeomorph L (EuclideanSpace ℝ (Fin n))),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) L ∧
    e = (cosetPartialHomeo hG₀_open ψ g).trans c }
  chartAt x := (cosetPartialHomeo hG₀_open ψ x).trans (chartAt (EuclideanSpace ℝ (Fin n)) (1 : L))
  mem_chart_source x := by
    refine ⟨?_, ?_⟩
    · show x⁻¹ * x ∈ Subgroup.connectedComponentOfOne G
      rw [inv_mul_cancel]
      exact (Subgroup.connectedComponentOfOne G).one_mem
    · have hm : x⁻¹ * x ∈ Subgroup.connectedComponentOfOne G := by
        rw [inv_mul_cancel]; exact (Subgroup.connectedComponentOfOne G).one_mem
      show (if h : x⁻¹ * x ∈ Subgroup.connectedComponentOfOne G then ψ ⟨x⁻¹ * x, h⟩ else 1) ∈
        (chartAt (EuclideanSpace ℝ (Fin n)) (1 : L)).source
      rw [dif_pos hm]
      have h1 : (⟨x⁻¹ * x, hm⟩ : Subgroup.connectedComponentOfOne G) = 1 :=
        Subtype.ext (inv_mul_cancel x)
      rw [h1, map_one]
      exact mem_chart_source _ (1 : L)
  chart_mem_atlas x := ⟨x, chartAt (EuclideanSpace ℝ (Fin n)) (1 : L), chart_mem_atlas _ 1, rfl⟩

private lemma admitsLieGroupStructure_of_openSubgroup
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (G' : Subgroup G) (hG'_open : IsOpen (G' : Set G))
    (hLieG' : AdmitsLieGroupStructure G')
    (hCartan : ∀ (n : ℕ) (L : Type) [Group L] [TopologicalSpace L] [T2Space L]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) L] [IsManifold (𝓡 n) ω L] [LieGroup (𝓡 n) ω L]
      (α : L →* L), Continuous α → ContMDiff (𝓡 n) (𝓡 n) ω α) :
    AdmitsLieGroupStructure G := by
  obtain ⟨n, ⟨pres⟩⟩ := hLieG'
  let L : Type := pres.carrier
  let _ : TopologicalSpace L := pres.topologicalSpace
  let _ : Group L := pres.group
  have _ : T2Space L := pres.t2Space
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) L := pres.chartedSpace
  have _ : IsManifold (𝓡 n) ω L := pres.isManifold
  have _ : LieGroup (𝓡 n) ω L := pres.lieGroup
  have _ : IsTopologicalGroup L :=
    { continuous_mul := (contMDiff_mul (I := 𝓡 n) (n := ω) (G := L)).continuous
      continuous_inv := (contMDiff_inv (𝓡 n) ω (G := L)).continuous }
  let ψ' : G' ≃ₜ* L := pres.equiv
  let L₀ : Subgroup L := Subgroup.connectedComponentOfOne L
  have hL₀_open : IsOpen (L₀ : Set L) := isOpen_connectedComponent_one (n := n)
  let G₀ : Subgroup G := Subgroup.connectedComponentOfOne G
  have hG₀_le : G₀ ≤ G' := connectedComponentOfOne_le_of_isOpen G' hG'_open
  have hG₀_eq : (G₀ : Set G) = ((↑) : G' → G) '' (Subgroup.connectedComponentOfOne G' : Set G') :=
    connectedComponentOfOne_eq_image_openSubgroup G' hG'_open
  have hψ'_cont : Continuous (ψ' : G' → L) := ψ'.continuous
  have hψ's_cont : Continuous (ψ'.symm : L → G') := ψ'.symm.continuous
  have hG'₀_open : IsOpen (Subgroup.connectedComponentOfOne G' : Set G') := by
    have hpre : (Subgroup.connectedComponentOfOne G' : Set G') = ψ' ⁻¹' (L₀ : Set L) := by
      ext x
      constructor
      · intro hx
        have himg := hψ'_cont.image_connectedComponent_subset (1 : G')
        rw [map_one] at himg
        exact himg ⟨x, hx, rfl⟩
      · intro hx
        have himg := hψ's_cont.image_connectedComponent_subset (1 : L)
        rw [map_one] at himg
        have hmem : ψ'.symm (ψ' x) ∈ connectedComponent (1 : G') := himg ⟨ψ' x, hx, rfl⟩
        rw [ψ'.symm_apply_apply] at hmem
        exact hmem
    rw [hpre]
    exact hL₀_open.preimage hψ'_cont
  have hG₀_open : IsOpen (G₀ : Set G) := by
    rw [hG₀_eq]
    exact hG'_open.isOpenEmbedding_subtypeVal.isOpenMap _ hG'₀_open
  have hG₀_normal : G₀.Normal := connectedComponentOfOne_normal
  have hψ'_mem : ∀ x : G₀, ψ' ⟨x.1, hG₀_le x.2⟩ ∈ L₀ := by
    intro x
    have hx' : (⟨x.1, hG₀_le x.2⟩ : G') ∈ Subgroup.connectedComponentOfOne G' := by
      have hx_img : x.1 ∈ ((↑) : G' → G) '' (Subgroup.connectedComponentOfOne G' : Set G') := by
        rw [← hG₀_eq]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx_img
      have hy_eq : y = ⟨x.1, hG₀_le x.2⟩ := Subtype.ext hyx
      rwa [← hy_eq]
    have himg := hψ'_cont.image_connectedComponent_subset (1 : G')
    rw [map_one] at himg
    exact himg ⟨⟨x.1, hG₀_le x.2⟩, hx', rfl⟩
  have hψ's_mem : ∀ y : L₀, (ψ'.symm y.1 : G) ∈ G₀ := by
    intro y
    have hy' : ψ'.symm y.1 ∈ Subgroup.connectedComponentOfOne G' := by
      have himg := hψ's_cont.image_connectedComponent_subset (1 : L)
      rw [map_one] at himg
      exact himg ⟨y.1, y.2, rfl⟩
    rw [← SetLike.mem_coe, hG₀_eq]
    exact ⟨ψ'.symm y.1, hy', rfl⟩
  let ψ : G₀ ≃ₜ* L₀ :=
    { toFun := fun x => ⟨ψ' ⟨x.1, hG₀_le x.2⟩, hψ'_mem x⟩
      invFun := fun y => ⟨(ψ'.symm y.1 : G), hψ's_mem y⟩
      left_inv := fun x => by
        apply Subtype.ext
        change (ψ'.symm (ψ' ⟨x.1, hG₀_le x.2⟩) : G) = x.1
        rw [ψ'.symm_apply_apply]
      right_inv := fun y => by
        apply Subtype.ext
        change ψ' ⟨(ψ'.symm y.1 : G), hG₀_le (hψ's_mem y)⟩ = y.1
        exact ψ'.apply_symm_apply y.1
      map_mul' := fun x₁ x₂ => by
        apply Subtype.ext
        change ψ' ⟨x₁.1 * x₂.1, hG₀_le (x₁ * x₂).2⟩ =
          ψ' ⟨x₁.1, hG₀_le x₁.2⟩ * ψ' ⟨x₂.1, hG₀_le x₂.2⟩
        rw [← map_mul]
        rfl
      continuous_toFun := by
        refine Continuous.subtype_mk (hψ'_cont.comp (Continuous.subtype_mk continuous_subtype_val _)) _
      continuous_invFun := by
        refine Continuous.subtype_mk (continuous_subtype_val.comp (hψ's_cont.comp continuous_subtype_val)) _ }
  let csL₀ : ChartedSpace (EuclideanSpace ℝ (Fin n)) L₀ := openSubgroupChartedSpace L₀ hL₀_open
  have hManL₀ : IsManifold (𝓡 n) ω L₀ := openSubgroup_isManifold L₀ hL₀_open
  have hLieL₀ : LieGroup (𝓡 n) ω L₀ := openSubgroup_lieGroup L₀ hL₀_open
  let csG : ChartedSpace (EuclideanSpace ℝ (Fin n)) G := cosetChartedSpace hG₀_open ψ
  have hManG : IsManifold (𝓡 n) ω G := by
    refine isManifold_of_contDiffOn (𝓡 n) ω G fun e₁ e₂ he₁ he₂ => ?_
    obtain ⟨g₁, c₁, hc₁, rfl⟩ := he₁
    obtain ⟨g₂, c₂, hc₂, rfl⟩ := he₂
    let τ₁ := cosetPartialHomeo hG₀_open ψ g₁
    let τ₂ := cosetPartialHomeo hG₀_open ψ g₂
    simp only [modelWithCornersSelf_coe, Function.comp_id, Function.id_comp,
      modelWithCornersSelf_coe_symm, Set.preimage_id, Set.range_id, Set.inter_univ]
    by_cases hne : ((τ₁.trans c₁).symm ≫ₕ (τ₂.trans c₂)).source.Nonempty
    · obtain ⟨y₀, hy₀⟩ := hne
      have hy₀_t1 : y₀ ∈ (τ₁.trans c₁).target := hy₀.1
      have hx₀_s1 : (τ₁.trans c₁).symm y₀ ∈ (τ₁.trans c₁).source :=
        (τ₁.trans c₁).map_target hy₀_t1
      have hx₀_s2 : (τ₁.trans c₁).symm y₀ ∈ (τ₂.trans c₂).source := hy₀.2
      have h1 : g₁⁻¹ * (τ₁.trans c₁).symm y₀ ∈ G₀ := hx₀_s1.1
      have h2 : g₂⁻¹ * (τ₁.trans c₁).symm y₀ ∈ G₀ := hx₀_s2.1
      have hu : g₂⁻¹ * g₁ ∈ G₀ := by
        have heq : g₂⁻¹ * g₁ =
            (g₂⁻¹ * (τ₁.trans c₁).symm y₀) * (g₁⁻¹ * (τ₁.trans c₁).symm y₀)⁻¹ := by group
        rw [heq]
        exact G₀.mul_mem h2 (G₀.inv_mem h1)
      let h : L₀ := ψ ⟨g₂⁻¹ * g₁, hu⟩
      have hmul_mdiff : ContMDiff (𝓡 n) (𝓡 n) ω (fun z : L₀ => h * z) := contMDiff_mul_left
      let s : Set L₀ := c₁.source ∩ (fun z : L₀ => h * z) ⁻¹' c₂.source
      have hs_sub : s ⊆ c₁.source := Set.inter_subset_left
      have hs_maps : MapsTo (fun z : L₀ => h * z) s c₂.source := fun _ hz => hz.2
      have hcd : ContDiffOn ℝ ω (c₂.extend (𝓡 n) ∘ (fun z : L₀ => h * z) ∘ (c₁.extend (𝓡 n)).symm)
          (c₁.extend (𝓡 n) '' s) :=
        (contMDiffOn_iff_of_mem_maximalAtlas'
          ((contDiffGroupoid ω (𝓡 n)).subset_maximalAtlas hc₁)
          ((contDiffGroupoid ω (𝓡 n)).subset_maximalAtlas hc₂)
          hs_sub hs_maps).mp (hmul_mdiff.contMDiffOn)
      have hsrc_eq : ((τ₁.trans c₁).symm ≫ₕ (τ₂.trans c₂)).source = c₁.extend (𝓡 n) '' s := by
        ext y
        constructor
        · intro hy
          have hy_t1 : y ∈ c₁.target := hy.1.1
          have hz_s1 : c₁.symm y ∈ c₁.source := c₁.map_target hy_t1
          have hx_s2 : g₁ * (ψ.symm (c₁.symm y) : G) ∈ (τ₂.trans c₂).source := hy.2
          have hhz : h * c₁.symm y ∈ c₂.source := by
            have hmem : g₂⁻¹ * (g₁ * (ψ.symm (c₁.symm y) : G)) ∈ G₀ := hx_s2.1
            have hval : τ₂ (g₁ * (ψ.symm (c₁.symm y) : G)) = h * c₁.symm y := by
              show (if hm : g₂⁻¹ * (g₁ * (ψ.symm (c₁.symm y) : G)) ∈ G₀ then
                ψ ⟨g₂⁻¹ * (g₁ * (ψ.symm (c₁.symm y) : G)), hm⟩ else 1) = h * c₁.symm y
              rw [dif_pos hmem]
              have hprod : (⟨g₂⁻¹ * (g₁ * (ψ.symm (c₁.symm y) : G)), hmem⟩ : G₀) =
                  ⟨g₂⁻¹ * g₁, hu⟩ * ψ.symm (c₁.symm y) := Subtype.ext (by simp [mul_assoc])
              rw [hprod, map_mul, ContinuousMulEquiv.apply_symm_apply]
            have hmem2 : τ₂ (g₁ * (ψ.symm (c₁.symm y) : G)) ∈ c₂.source := hx_s2.2
            rwa [hval] at hmem2
          refine ⟨c₁.symm y, ⟨hz_s1, hhz⟩, ?_⟩
          simpa using c₁.right_inv hy_t1
        · rintro ⟨z, ⟨hz_s1, hhz⟩, rfl⟩
          have hy_t1 : c₁ z ∈ c₁.target := c₁.map_source hz_s1
          have hinv : c₁.symm (c₁ z) = z := c₁.left_inv hz_s1
          have hmem : g₂⁻¹ * (g₁ * (ψ.symm z : G)) ∈ G₀ := by
            rw [← mul_assoc]; exact G₀.mul_mem hu (ψ.symm z).2
          have hval : τ₂ (g₁ * (ψ.symm z : G)) = h * z := by
            show (if hm : g₂⁻¹ * (g₁ * (ψ.symm z : G)) ∈ G₀ then
              ψ ⟨g₂⁻¹ * (g₁ * (ψ.symm z : G)), hm⟩ else 1) = h * z
            rw [dif_pos hmem]
            have hprod : (⟨g₂⁻¹ * (g₁ * (ψ.symm z : G)), hmem⟩ : G₀) =
                ⟨g₂⁻¹ * g₁, hu⟩ * ψ.symm z := Subtype.ext (by simp [mul_assoc])
            rw [hprod, map_mul, ContinuousMulEquiv.apply_symm_apply]
          refine ⟨⟨hy_t1, trivial⟩, ?_⟩
          show g₁ * (ψ.symm (c₁.symm (c₁ z)) : G) ∈ (τ₂.trans c₂).source
          rw [hinv]
          refine ⟨hmem, ?_⟩
          show τ₂ (g₁ * (ψ.symm z : G)) ∈ c₂.source
          rwa [hval]
      rw [hsrc_eq]
      refine hcd.congr fun y hy => ?_
      obtain ⟨z, ⟨hz_s1, _⟩, rfl⟩ := hy
      have hinv : c₁.symm (c₁ z) = z := c₁.left_inv hz_s1
      have hmem : g₂⁻¹ * (g₁ * (ψ.symm z : G)) ∈ G₀ := by
        rw [← mul_assoc]; exact G₀.mul_mem hu (ψ.symm z).2
      have hval : τ₂ (g₁ * (ψ.symm z : G)) = h * z := by
        show (if hm : g₂⁻¹ * (g₁ * (ψ.symm z : G)) ∈ G₀ then
          ψ ⟨g₂⁻¹ * (g₁ * (ψ.symm z : G)), hm⟩ else 1) = h * z
        rw [dif_pos hmem]
        have hprod : (⟨g₂⁻¹ * (g₁ * (ψ.symm z : G)), hmem⟩ : G₀) =
            ⟨g₂⁻¹ * g₁, hu⟩ * ψ.symm z := Subtype.ext (by simp [mul_assoc])
        rw [hprod, map_mul, ContinuousMulEquiv.apply_symm_apply]
      show c₂ (τ₂ (g₁ * (ψ.symm (c₁.symm (c₁ z)) : G))) = c₂ (h * c₁.symm (c₁ z))
      rw [hinv, hval]
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact contDiffOn_empty
  have hconj_mdiff : ∀ g : G,
      let α : L₀ →* L₀ :=
        { toFun := fun z => ψ ⟨g⁻¹ * (ψ.symm z : G) * g, by
            have := hG₀_normal.conj_mem (ψ.symm z : G) (ψ.symm z).2 g⁻¹
            simpa [inv_inv] using this⟩
          map_one' := by simp
          map_mul' := fun z₁ z₂ => by
            rw [← map_mul]; congr 1; apply Subtype.ext; simp [mul_assoc] }
      ContMDiff (𝓡 n) (𝓡 n) ω α := by
    intro g α
    refine hCartan n L₀ α ?_
    refine ψ.continuous.comp (Continuous.subtype_mk ?_ _)
    exact (continuous_const.mul (continuous_subtype_val.comp ψ.symm.continuous)).mul continuous_const
  have hLieG : LieGroup (𝓡 n) ω G := by
    let c₀ := chartAt (EuclideanSpace ℝ (Fin n)) (1 : L₀)
    have hmulG : ContMDiff ((𝓡 n).prod (𝓡 n)) (𝓡 n) ω (fun p : G × G => p.1 * p.2) := by
      intro ⟨g₁, g₂⟩
      rw [contMDiffAt_iff]
      refine ⟨continuous_mul.continuousAt, ?_⟩
      let α : L₀ →* L₀ :=
        { toFun := fun z => ψ ⟨g₂⁻¹ * (ψ.symm z : G) * g₂, by
            have := hG₀_normal.conj_mem (ψ.symm z : G) (ψ.symm z).2 g₂⁻¹
            simpa [inv_inv] using this⟩
          map_one' := by simp
          map_mul' := fun z₁ z₂ => by
            rw [← map_mul]; congr 1; apply Subtype.ext; simp [mul_assoc] }
      have hα_mdiff : ContMDiff (𝓡 n) (𝓡 n) ω α := hconj_mdiff g₂
      let F : L₀ × L₀ → L₀ := fun p => α p.1 * p.2
      have hF_mdiff : ContMDiff ((𝓡 n).prod (𝓡 n)) (𝓡 n) ω F :=
        (hα_mdiff.comp contMDiff_fst).mul contMDiff_snd
      have hF_at := (contMDiffAt_iff.mp (hF_mdiff (1, 1))).2
      have hchart_at1 : extChartAt ((𝓡 n).prod (𝓡 n)) (g₁, g₂) (g₁, g₂) =
          extChartAt ((𝓡 n).prod (𝓡 n)) ((1 : L₀), (1 : L₀)) (1, 1) := by
        have h1 : chartAt (EuclideanSpace ℝ (Fin n)) g₁ g₁ = c₀ 1 := by
          change c₀ (cosetPartialHomeo hG₀_open ψ g₁ g₁) = c₀ 1
          have hm : g₁⁻¹ * g₁ ∈ G₀ := by rw [inv_mul_cancel]; exact G₀.one_mem
          have hτ : cosetPartialHomeo hG₀_open ψ g₁ g₁ = 1 := by
            show (if h : g₁⁻¹ * g₁ ∈ G₀ then ψ ⟨g₁⁻¹ * g₁, h⟩ else 1) = 1
            rw [dif_pos hm]
            have : (⟨g₁⁻¹ * g₁, hm⟩ : G₀) = 1 := Subtype.ext (inv_mul_cancel g₁)
            rw [this, map_one]
          rw [hτ]
        have h2 : chartAt (EuclideanSpace ℝ (Fin n)) g₂ g₂ = c₀ 1 := by
          change c₀ (cosetPartialHomeo hG₀_open ψ g₂ g₂) = c₀ 1
          have hm : g₂⁻¹ * g₂ ∈ G₀ := by rw [inv_mul_cancel]; exact G₀.one_mem
          have hτ : cosetPartialHomeo hG₀_open ψ g₂ g₂ = 1 := by
            show (if h : g₂⁻¹ * g₂ ∈ G₀ then ψ ⟨g₂⁻¹ * g₂, h⟩ else 1) = 1
            rw [dif_pos hm]
            have : (⟨g₂⁻¹ * g₂, hm⟩ : G₀) = 1 := Subtype.ext (inv_mul_cancel g₂)
            rw [this, map_one]
          rw [hτ]
        simp [extChartAt, h1, h2, c₀]
      rw [hchart_at1]
      have hF1 : F (1, 1) = 1 := by simp [F]
      rw [hF1] at hF_at
      have hfun : (extChartAt (𝓡 n) ((g₁, g₂).1 * (g₁, g₂).2) ∘ (fun p : G × G => p.1 * p.2) ∘
          (extChartAt ((𝓡 n).prod (𝓡 n)) (g₁, g₂)).symm) =
          (extChartAt (𝓡 n) (1 : L₀) ∘ F ∘ (extChartAt ((𝓡 n).prod (𝓡 n)) ((1 : L₀), (1 : L₀))).symm) := by
        funext ⟨y₁, y₂⟩
        show c₀ (cosetPartialHomeo hG₀_open ψ (g₁ * g₂)
            ((g₁ * (ψ.symm (c₀.symm y₁) : G)) * (g₂ * (ψ.symm (c₀.symm y₂) : G)))) =
          c₀ (α (c₀.symm y₁) * c₀.symm y₂)
        congr 1
        have hconj_mem : g₂⁻¹ * (ψ.symm (c₀.symm y₁) : G) * g₂ ∈ G₀ := by
          have := hG₀_normal.conj_mem (ψ.symm (c₀.symm y₁) : G) (ψ.symm (c₀.symm y₁)).2 g₂⁻¹
          simpa [inv_inv] using this
        have hprod_eq : (g₁ * g₂)⁻¹ * ((g₁ * (ψ.symm (c₀.symm y₁) : G)) * (g₂ * (ψ.symm (c₀.symm y₂) : G))) =
            (g₂⁻¹ * (ψ.symm (c₀.symm y₁) : G) * g₂) * (ψ.symm (c₀.symm y₂) : G) := by group
        have hmem : (g₁ * g₂)⁻¹ * ((g₁ * (ψ.symm (c₀.symm y₁) : G)) * (g₂ * (ψ.symm (c₀.symm y₂) : G))) ∈ G₀ := by
          rw [hprod_eq]; exact G₀.mul_mem hconj_mem (ψ.symm (c₀.symm y₂)).2
        show (if hm : (g₁ * g₂)⁻¹ * ((g₁ * (ψ.symm (c₀.symm y₁) : G)) * (g₂ * (ψ.symm (c₀.symm y₂) : G))) ∈ G₀ then
          ψ ⟨_, hm⟩ else 1) = α (c₀.symm y₁) * c₀.symm y₂
        rw [dif_pos hmem]
        have hsub : (⟨(g₁ * g₂)⁻¹ * ((g₁ * (ψ.symm (c₀.symm y₁) : G)) * (g₂ * (ψ.symm (c₀.symm y₂) : G))), hmem⟩ : G₀) =
            ⟨g₂⁻¹ * (ψ.symm (c₀.symm y₁) : G) * g₂, hconj_mem⟩ * ψ.symm (c₀.symm y₂) :=
          Subtype.ext hprod_eq
        rw [hsub, map_mul, ContinuousMulEquiv.apply_symm_apply]
        rfl
      rw [hfun]
      exact hF_at
    have hinvG : ContMDiff (𝓡 n) (𝓡 n) ω (fun a : G => a⁻¹) := by
      intro g
      rw [contMDiffAt_iff]
      refine ⟨continuous_inv.continuousAt, ?_⟩
      let α : L₀ →* L₀ :=
        { toFun := fun z => ψ ⟨(g⁻¹)⁻¹ * (ψ.symm z : G) * g⁻¹, by
            have := hG₀_normal.conj_mem (ψ.symm z : G) (ψ.symm z).2 g
            simpa [inv_inv] using this⟩
          map_one' := by simp
          map_mul' := fun z₁ z₂ => by
            rw [← map_mul]; congr 1; apply Subtype.ext; simp [mul_assoc] }
      have hα_mdiff : ContMDiff (𝓡 n) (𝓡 n) ω α := hconj_mdiff g⁻¹
      let F : L₀ → L₀ := fun z => α z⁻¹
      have hF_mdiff : ContMDiff (𝓡 n) (𝓡 n) ω F := hα_mdiff.comp (contMDiff_inv (𝓡 n) ω)
      have hF_at := (contMDiffAt_iff.mp (hF_mdiff (1 : L₀))).2
      have hchart_at1 : extChartAt (𝓡 n) g g = extChartAt (𝓡 n) (1 : L₀) (1 : L₀) := by
        have h1 : chartAt (EuclideanSpace ℝ (Fin n)) g g = c₀ 1 := by
          change c₀ (cosetPartialHomeo hG₀_open ψ g g) = c₀ 1
          have hm : g⁻¹ * g ∈ G₀ := by rw [inv_mul_cancel]; exact G₀.one_mem
          have hτ : cosetPartialHomeo hG₀_open ψ g g = 1 := by
            show (if h : g⁻¹ * g ∈ G₀ then ψ ⟨g⁻¹ * g, h⟩ else 1) = 1
            rw [dif_pos hm]
            have : (⟨g⁻¹ * g, hm⟩ : G₀) = 1 := Subtype.ext (inv_mul_cancel g)
            rw [this, map_one]
          rw [hτ]
        simp [extChartAt, h1, c₀]
      rw [hchart_at1]
      have hF1 : F 1 = 1 := by simp [F]
      rw [hF1] at hF_at
      have hfun : (extChartAt (𝓡 n) g⁻¹ ∘ (fun a : G => a⁻¹) ∘ (extChartAt (𝓡 n) g).symm) =
          (extChartAt (𝓡 n) (1 : L₀) ∘ F ∘ (extChartAt (𝓡 n) (1 : L₀)).symm) := by
        funext y
        show c₀ (cosetPartialHomeo hG₀_open ψ g⁻¹ (g * (ψ.symm (c₀.symm y) : G))⁻¹) =
          c₀ (α (c₀.symm y)⁻¹)
        congr 1
        have hinv_eq : (g⁻¹)⁻¹ * (g * (ψ.symm (c₀.symm y) : G))⁻¹ =
            (g⁻¹)⁻¹ * (ψ.symm (c₀.symm y)⁻¹ : G) * g⁻¹ := by
          have hsymm_inv : (ψ.symm (c₀.symm y)⁻¹ : G) = (ψ.symm (c₀.symm y) : G)⁻¹ := by
            rw [map_inv]; rfl
          rw [hsymm_inv]; group
        have hmem : (g⁻¹)⁻¹ * (g * (ψ.symm (c₀.symm y) : G))⁻¹ ∈ G₀ := by
          rw [hinv_eq]
          have := hG₀_normal.conj_mem (ψ.symm (c₀.symm y)⁻¹ : G) (ψ.symm (c₀.symm y)⁻¹).2 g
          simpa [inv_inv] using this
        show (if hm : (g⁻¹)⁻¹ * (g * (ψ.symm (c₀.symm y) : G))⁻¹ ∈ G₀ then
          ψ ⟨_, hm⟩ else 1) = α (c₀.symm y)⁻¹
        rw [dif_pos hmem]
        exact congrArg ψ (Subtype.ext hinv_eq)
      rw [hfun]
      exact hF_at
    exact { contMDiff_mul := hmulG, contMDiff_inv := hinvG }
  exact ⟨n, ⟨{
    carrier := G
    topologicalSpace := inferInstance
    group := inferInstance
    t2Space := inferInstance
    chartedSpace := csG
    isManifold := hManG
    lieGroup := hLieG
    equiv := ContinuousMulEquiv.refl G
  }⟩⟩

private lemma admitsLieGroupStructure_of_quotient_bot
    {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    (K : Subgroup G') [K.Normal] (hK : K = ⊥)
    (hLie : AdmitsLieGroupStructure (G' ⧸ K)) :
    AdmitsLieGroupStructure G' := by
  have hbij : Function.Bijective (QuotientGroup.mk' K) := by
    refine ⟨?_, QuotientGroup.mk'_surjective K⟩
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hK
  let eMul : G' ≃* (G' ⧸ K) := MulEquiv.ofBijective (QuotientGroup.mk' K) hbij
  have hopen : IsOpenMap eMul := QuotientGroup.isOpenMap_coe
  let eTop : G' ≃ₜ* (G' ⧸ K) :=
    { toMulEquiv := eMul
      continuous_toFun := continuous_quot_mk
      continuous_invFun := by
        rw [continuous_def]
        intro U hU
        have hpre : eMul.symm ⁻¹' U = eMul '' U := by
          ext y
          constructor
          · intro hy; exact ⟨eMul.symm y, hy, eMul.apply_symm_apply y⟩
          · rintro ⟨x, hx, rfl⟩; simpa using hx
        change IsOpen (eMul.symm ⁻¹' U)
        rw [hpre]
        exact hopen U hU }
  obtain ⟨n, ⟨p⟩⟩ := hLie
  let _ : TopologicalSpace p.carrier := p.topologicalSpace
  let _ : Group p.carrier := p.group
  exact ⟨n, ⟨{
    carrier := p.carrier
    topologicalSpace := p.topologicalSpace
    group := p.group
    t2Space := p.t2Space
    chartedSpace := p.chartedSpace
    isManifold := p.isManifold
    lieGroup := p.lieGroup
    equiv := eTop.trans p.equiv
  }⟩⟩

/- ### Part 4: Hypotheses and main reduction theorem -/

/-- **Gleason–Yamabe approximation theorem** (Yamabe 1953):
every locally compact Hausdorff topological group `G : Type` has an open subgroup `G' ≤ G`
such that every open neighborhood `V` of `1` in `G` contains a compact normal subgroup `K ◁ G'`
whose quotient `G' ⧸ K` admits a Lie group structure. -/
def H1 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G],
    ∃ G' : Subgroup G, IsOpen (G' : Set G) ∧
      ∀ V : Set G, IsOpen V → (1 : G) ∈ V →
        ∃ (K : Subgroup G') (_ : K.Normal), IsCompact (K : Set G') ∧
          (((↑) : G' → G) '' (K : Set G')) ⊆ V ∧ AdmitsLieGroupStructure (G' ⧸ K)

/-- **Cartan's automatic analyticity theorem**:
every continuous endomorphism of a finite-dimensional real-analytic Lie group `L : Type`
is real-analytic. -/
def H2 : Prop :=
  ∀ (n : ℕ) (L : Type) [Group L] [TopologicalSpace L] [T2Space L]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) L] [IsManifold (𝓡 n) ω L] [LieGroup (𝓡 n) ω L]
    (α : L →* L), Continuous α → ContMDiff (𝓡 n) (𝓡 n) ω α

theorem main : H1 → H2 →
    OMA.R_Hilbert5_hilbert_smith_conjecture_variants_riemannian_R1.H3 := by
  intro h1 h2
  dsimp only [OMA.R_Hilbert5_hilbert_smith_conjecture_variants_riemannian_R1.H3]
  intro G _ _ _ _ _ hNSS
  obtain ⟨V, hV_open, h1V, hV_nss⟩ := hNSS
  obtain ⟨G', hG'_open, hYamabe⟩ := h1 G
  obtain ⟨K, hK_norm, _, hK_sub, hK_lie⟩ := hYamabe V hV_open h1V
  have hK_map_bot : K.map G'.subtype = ⊥ := by
    apply hV_nss (K.map G'.subtype)
    rintro _ ⟨x, hxK, rfl⟩
    exact hK_sub ⟨x, hxK, rfl⟩
  have hK_bot : K = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hxK
    have hmem : (x : G) ∈ K.map G'.subtype := ⟨x, hxK, rfl⟩
    rw [hK_map_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hmem))
  have hLieG' : AdmitsLieGroupStructure G' :=
    admitsLieGroupStructure_of_quotient_bot K hK_bot hK_lie
  exact admitsLieGroupStructure_of_openSubgroup G' hG'_open hLieG' h2

end OMA.R_Hilbert5_hilbert_smith_conjecture_variants_riemannian_R1_H3_R1

end
