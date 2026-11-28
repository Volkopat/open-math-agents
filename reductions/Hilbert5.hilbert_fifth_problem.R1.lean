import FormalConjectures.HilbertProblems.«5»
import Mathlib.Logic.Small.List
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Reduction of `Hilbert5.hilbert_fifth_problem` (Hilbert's Fifth Problem)

Following Gleason (1952), Montgomery–Zippin (1952), and Yamabe (1953) (see also van den
Dries–Goldbring 2015), we reduce `Hilbert5.hilbert_fifth_problem` (for a locally Euclidean
Hausdorff topological group $G$ in an arbitrary universe `Type u` with arbitrarily many connected
components) to three canonical theorems of Lie theory stated in `Type`:
1. (`H1`) **No Small Subgroups (Gleason–Montgomery–Zippin)**: every connected Hausdorff
   topological group in `Type` modeled on $\mathbb{R}^n$ has no small subgroups.
2. (`H2`) **NSS $\Rightarrow$ Lie (Gleason–Yamabe–Montgomery–Zippin)**: every connected
   Hausdorff topological group in `Type` modeled on $\mathbb{R}^n$ with no small subgroups admits
   an $n$-dimensional real-analytic `LieGroupPresentation`.
3. (`H3`) **Cartan's Automatic Analyticity**: every continuous group automorphism of a
   finite-dimensional real-analytic Lie group in `Type` is real-analytic (`ContMDiff (𝓡 n) (𝓡 n) ω`).

Inside `main`, we prove:
- The identity component $G_0 = \mathrm{connectedComponent}(1)$ is an open normal subgroup of $G$
  modeled on $\mathbb{R}^n$.
- **Universe descent (`Small.{0} G₀`)**: since $G_0$ is connected and locally Euclidean, a
  symmetric chart neighborhood $V \subseteq G_0$ injects into $\mathbb{R}^n : \mathrm{Type}$ and
  generates $G_0$, so $\mathrm{List}\, V \twoheadrightarrow G_0$ yields `Small.{0} G₀`.
- Transporting $G_0$ to `Shrink.{0} G₀ : Type`, `H1` and `H2` give a real-analytic Lie group $L$
  continuously isomorphic to $G_0$.
- Left-translating the analytic atlas of $L$ onto every coset $g G_0 \subseteq G$ builds a
  compatible real-analytic `ChartedSpace`, `IsManifold (𝓡 n) ω G`, and (using `H3` for the
  conjugation automorphisms on $L$) `LieGroup (𝓡 n) ω G` on all of $G : \mathrm{Type}\ u$.
-/

-- Reduction Hilbert5.hilbert_fifth_problem.R1 of Hilbert's fifth problem
-- Credit: @tkaiman
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Set Topology Filter TopologicalSpace
open scoped Manifold ContDiff Pointwise Classical

noncomputable section

namespace OMA.R_Hilbert5_hilbert_fifth_problem_R1

/- ### Step 1: Identity component is an open normal subgroup modeled on `ℝ^n` -/

private lemma isOpen_connectedComponent_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) G] :
    IsOpen (connectedComponent (1 : G)) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hmem_t : e x ∈ e.target := e.map_source (mem_chart_source _ x)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) hmem_t
  let U : Set G := e.source ∩ e ⁻¹' Metric.ball (e x) r
  have hU_open : IsOpen U := e.continuousOn_toFun.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  have hxU : x ∈ U := ⟨mem_chart_source _ x, Metric.mem_ball_self hr⟩
  have hU_eq : U = e.symm '' Metric.ball (e x) r := by
    ext y
    constructor
    · rintro ⟨hy_s, hy_b⟩
      exact ⟨e y, hy_b, e.left_inv hy_s⟩
    · rintro ⟨z, hz_b, rfl⟩
      have hz_t : z ∈ e.target := hball hz_b
      exact ⟨e.map_target hz_t, by show e (e.symm z) ∈ Metric.ball (e x) r; rw [e.right_inv hz_t]; exact hz_b⟩
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

private lemma connectedSpace_connectedComponentOfOne {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    ConnectedSpace (Subgroup.connectedComponentOfOne G) := by
  have hconn : IsConnected ((Subgroup.connectedComponentOfOne G : Set G)) :=
    isConnected_connectedComponent
  exact Subtype.connectedSpace hconn

/- ### Step 2: Universe descent `Small.{0} (Subgroup.connectedComponentOfOne G)` -/

private lemma small_connectedComponentOfOne {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) G] :
    Small.{0} (Subgroup.connectedComponentOfOne G) := by
  let G₀ := Subgroup.connectedComponentOfOne G
  have hG₀_open : IsOpen (G₀ : Set G) := isOpen_connectedComponent_one (n := n)
  let e := chartAt (EuclideanSpace ℝ (Fin n)) (1 : G)
  let W : Set G := e.source ∩ (G₀ : Set G)
  have hW_open : IsOpen W := e.open_source.inter hG₀_open
  have h1W : (1 : G) ∈ W := ⟨mem_chart_source _ 1, mem_connectedComponent⟩
  let V : Set G₀ := ((↑) : G₀ → G) ⁻¹' (W ∩ W⁻¹)
  have hV_open : IsOpen V :=
    (hW_open.inter hW_open.inv).preimage continuous_subtype_val
  have h1V : (1 : G₀) ∈ V := ⟨h1W, by simpa using h1W⟩
  have hV_symm : ∀ v : G₀, v ∈ V → v⁻¹ ∈ V := by
    intro v hv
    exact ⟨by simpa using hv.2, by simpa using hv.1⟩
  have hV_small : Small.{0} V := by
    refine small_of_injective (f := fun v : V => e (v.1 : G)) ?_
    intro v₁ v₂ heq
    have hv₁ : (v₁.1 : G) ∈ e.source := v₁.2.1.1
    have hv₂ : (v₂.1 : G) ∈ e.source := v₂.2.1.1
    exact Subtype.ext (Subtype.ext (e.injOn hv₁ hv₂ heq))
  let K : Subgroup G₀ := Subgroup.closure V
  have hK_open : IsOpen (K : Set G₀) := by
    rw [isOpen_iff_mem_nhds]
    intro k hk
    have hsub : (fun x : G₀ => k * x) '' V ⊆ (K : Set G₀) := by
      rintro _ ⟨v, hv, rfl⟩
      exact K.mul_mem hk (Subgroup.subset_closure hv)
    have himg_open : IsOpen ((fun x : G₀ => k * x) '' V) :=
      (Homeomorph.mulLeft k).isOpenMap V hV_open
    exact Filter.mem_of_superset (himg_open.mem_nhds ⟨1, h1V, mul_one k⟩) hsub
  have hK_closed : IsClosed (K : Set G₀) := Subgroup.isClosed_of_isOpen K hK_open
  have : ConnectedSpace G₀ := connectedSpace_connectedComponentOfOne
  have hK_top : K = ⊤ := by
    have hclopen : IsClopen (K : Set G₀) := ⟨hK_closed, hK_open⟩
    have huniv : (K : Set G₀) = Set.univ :=
      hclopen.eq_univ ⟨1, K.one_mem⟩
    ext x
    simp only [Subgroup.mem_top, iff_true]
    show x ∈ (K : Set G₀)
    rw [huniv]
    trivial
  have hsurj : Function.Surjective (fun l : List V => (l.map fun v => v.1).prod) := by
    intro x
    have hxK : x ∈ K := by rw [hK_top]; trivial
    refine Subgroup.closure_induction (p := fun y _ => ∃ l : List V, (l.map fun v => v.1).prod = y)
      ?_ ?_ ?_ ?_ hxK
    · intro v hv; exact ⟨[⟨v, hv⟩], by simp⟩
    · exact ⟨[], by simp⟩
    · rintro y z _ _ ⟨l₁, rfl⟩ ⟨l₂, rfl⟩
      exact ⟨l₁ ++ l₂, by simp⟩
    · rintro y _ ⟨l, rfl⟩
      refine ⟨(l.map fun v => ⟨v.1⁻¹, hV_symm v.1 v.2⟩).reverse, ?_⟩
      have hrev : ∀ l : List V,
          ((l.map fun v => (⟨v.1⁻¹, hV_symm v.1 v.2⟩ : V)).reverse.map fun v => v.1).prod =
            (l.map fun v => v.1).prod⁻¹ := by
        intro l'
        induction l' with
        | nil => simp
        | cons a t ih =>
          simp only [List.map_cons, List.reverse_cons, List.map_append, List.map_nil,
            List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_inv_rev]
          rw [ih]
      exact hrev l
  have : Small.{0} V := hV_small
  exact small_of_surjective hsurj

/- ### Step 3: Transporting `ChartedSpace` to an open subgroup and along a homeomorphism -/

private abbrev openSubgroupChartedSpace {G : Type*} [Group G] [TopologicalSpace G]
    {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) U :=
  let inc : OpenPartialHomeomorph U G :=
    hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph ((↑) : U → G)
  { atlas := { inc.trans e | e ∈ atlas (EuclideanSpace ℝ (Fin n)) G }
    chartAt := fun x => inc.trans (chartAt (EuclideanSpace ℝ (Fin n)) (x : G))
    mem_chart_source := fun x => ⟨trivial, mem_chart_source _ (x : G)⟩
    chart_mem_atlas := fun x => ⟨chartAt (EuclideanSpace ℝ (Fin n)) (x : G), chart_mem_atlas _ _, rfl⟩ }

/- ### Step 4: Coset-translated real-analytic atlas on all of `G : Type u` -/

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

/- ### Hypotheses and main reduction theorem -/

/-- **No Small Subgroups theorem** (Gleason–Montgomery–Zippin, 1952): every connected Hausdorff
locally Euclidean topological group in `Type` has a neighborhood of the identity containing no
nontrivial subgroup. -/
def H1 : Prop :=
  ∀ (n : ℕ) (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [ConnectedSpace H] [ChartedSpace (EuclideanSpace ℝ (Fin n)) H],
    ∃ U : Set H, U ∈ 𝓝 (1 : H) ∧ ∀ K : Subgroup H, (K : Set H) ⊆ U → K = ⊥

/-- **NSS implies Lie** (Gleason–Yamabe–Montgomery–Zippin, 1952): every connected Hausdorff
locally Euclidean topological group in `Type` with no small subgroups admits an $n$-dimensional
real-analytic `LieGroupPresentation`. -/
def H2 : Prop :=
  ∀ (n : ℕ) (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [ConnectedSpace H] [ChartedSpace (EuclideanSpace ℝ (Fin n)) H],
    (∃ U : Set H, U ∈ 𝓝 (1 : H) ∧ ∀ K : Subgroup H, (K : Set H) ⊆ U → K = ⊥) →
    Nonempty (LieGroupPresentation H n)

/-- **Cartan's automatic analyticity theorem**: every continuous group homomorphism from a
finite-dimensional real-analytic Lie group in `Type` to itself is real-analytic. -/
def H3 : Prop :=
  ∀ (n : ℕ) (L : Type) [Group L] [TopologicalSpace L] [T2Space L]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) L] [IsManifold (𝓡 n) ω L] [LieGroup (𝓡 n) ω L]
    (α : L →* L), Continuous α → ContMDiff (𝓡 n) (𝓡 n) ω α

theorem main : H1 → H2 → H3 → type_of% @Hilbert5.hilbert_fifth_problem := by
  intro h1 h2 h3 G _ _ n _ _ _
  let G₀ := Subgroup.connectedComponentOfOne G
  have hG₀_open : IsOpen (G₀ : Set G) := isOpen_connectedComponent_one (n := n)
  have hG₀_normal : G₀.Normal := connectedComponentOfOne_normal
  have hG₀_conn : ConnectedSpace G₀ := connectedSpace_connectedComponentOfOne
  have hG₀_small : Small.{0} G₀ := small_connectedComponentOfOne (n := n)
  have : Small.{0} G₀ := hG₀_small
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G₀ := openSubgroupChartedSpace G₀ hG₀_open
  -- Transport G₀ to Type 0 via equivShrink (using Mathlib's Shrink.instGroup / Shrink.mulEquiv)
  let H : Type := Shrink.{0} G₀
  let eMul : G₀ ≃* H := (Shrink.mulEquiv (α := G₀)).symm
  let : TopologicalSpace H := TopologicalSpace.coinduced eMul inferInstance
  let φ : G₀ ≃ₜ* H :=
    { toMulEquiv := eMul
      continuous_toFun := continuous_coinduced_rng
      continuous_invFun := by
        rw [continuous_coinduced_dom]
        convert continuous_id
        ext x; simp }
  have : IsTopologicalGroup H :=
    { continuous_mul := by
        have h : (fun p : H × H => p.1 * p.2) =
            fun p => φ (φ.symm p.1 * φ.symm p.2) := by
          ext ⟨x, y⟩
          simp [map_mul]
        rw [h]
        exact φ.continuous.comp ((φ.symm.continuous.comp continuous_fst).mul
          (φ.symm.continuous.comp continuous_snd))
      continuous_inv := by
        have h : (fun x : H => x⁻¹) = fun x => φ (φ.symm x)⁻¹ := by
          ext x
          simp [map_inv]
        rw [h]
        exact φ.continuous.comp (φ.symm.continuous.inv) }
  have : T2Space H := φ.toHomeomorph.symm.isEmbedding.t2Space
  have : ConnectedSpace H := φ.toHomeomorph.connectedSpace_iff.mp hG₀_conn
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) H := φ.toHomeomorph.chartedSpace
  -- Apply H1 and H2 in Type 0
  have hNSS := h1 n H
  obtain ⟨pres⟩ := h2 n H hNSS
  let L : Type := pres.carrier
  let : TopologicalSpace L := pres.topologicalSpace
  let : Group L := pres.group
  have : T2Space L := pres.t2Space
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) L := pres.chartedSpace
  have : IsManifold (𝓡 n) ω L := pres.isManifold
  have : LieGroup (𝓡 n) ω L := pres.lieGroup
  let ψ : G₀ ≃ₜ* L := φ.trans pres.equiv
  have : IsTopologicalGroup L :=
    { continuous_mul := (contMDiff_mul (I := 𝓡 n) (n := ω) (G := L)).continuous
      continuous_inv := (contMDiff_inv (𝓡 n) ω (G := L)).continuous }
  -- Define the coset-translated real-analytic charted space on G
  let csG : ChartedSpace (EuclideanSpace ℝ (Fin n)) G := cosetChartedSpace hG₀_open ψ
  -- Switch local ChartedSpace instance on G to csG
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G := csG
  -- Prove IsManifold (𝓡 n) ω G for csG
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
        have heq : g₂⁻¹ * g₁ = (g₂⁻¹ * (τ₁.trans c₁).symm y₀) * (g₁⁻¹ * (τ₁.trans c₁).symm y₀)⁻¹ := by
          group
        rw [heq]
        exact G₀.mul_mem h2 (G₀.inv_mem h1)
      let h : L := ψ ⟨g₂⁻¹ * g₁, hu⟩
      have hmul_mdiff : ContMDiff (𝓡 n) (𝓡 n) ω (fun z : L => h * z) := contMDiff_mul_left
      let s : Set L := c₁.source ∩ (fun z : L => h * z) ⁻¹' c₂.source
      have hs_sub : s ⊆ c₁.source := Set.inter_subset_left
      have hs_maps : MapsTo (fun z : L => h * z) s c₂.source := fun _ hz => hz.2
      have hcd : ContDiffOn ℝ ω (c₂.extend (𝓡 n) ∘ (fun z : L => h * z) ∘ (c₁.extend (𝓡 n)).symm)
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
                  ⟨g₂⁻¹ * g₁, hu⟩ * ψ.symm (c₁.symm y) :=
                Subtype.ext (by simp [mul_assoc])
              rw [hprod, map_mul, ContinuousMulEquiv.apply_symm_apply]
            have hmem2 : τ₂ (g₁ * (ψ.symm (c₁.symm y) : G)) ∈ c₂.source := hx_s2.2
            rwa [hval] at hmem2
          refine ⟨c₁.symm y, ⟨hz_s1, hhz⟩, ?_⟩
          simpa using c₁.right_inv hy_t1
        · rintro ⟨z, ⟨hz_s1, hhz⟩, rfl⟩
          have hy_t1 : c₁ z ∈ c₁.target := c₁.map_source hz_s1
          have hinv : c₁.symm (c₁ z) = z := c₁.left_inv hz_s1
          have hmem : g₂⁻¹ * (g₁ * (ψ.symm z : G)) ∈ G₀ := by
            have heq : g₂⁻¹ * (g₁ * (ψ.symm z : G)) = (g₂⁻¹ * g₁) * (ψ.symm z : G) := by
              rw [mul_assoc]
            rw [heq]
            exact G₀.mul_mem hu (ψ.symm z).2
          have hval : τ₂ (g₁ * (ψ.symm z : G)) = h * z := by
            show (if hm : g₂⁻¹ * (g₁ * (ψ.symm z : G)) ∈ G₀ then
              ψ ⟨g₂⁻¹ * (g₁ * (ψ.symm z : G)), hm⟩ else 1) = h * z
            rw [dif_pos hmem]
            have hprod : (⟨g₂⁻¹ * (g₁ * (ψ.symm z : G)), hmem⟩ : G₀) =
                ⟨g₂⁻¹ * g₁, hu⟩ * ψ.symm z :=
              Subtype.ext (by simp [mul_assoc])
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
            ⟨g₂⁻¹ * g₁, hu⟩ * ψ.symm z :=
          Subtype.ext (by simp [mul_assoc])
        rw [hprod, map_mul, ContinuousMulEquiv.apply_symm_apply]
      show c₂ (τ₂ (g₁ * (ψ.symm (c₁.symm (c₁ z)) : G))) =
        c₂ (h * c₁.symm (c₁ z))
      rw [hinv, hval]
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact contDiffOn_empty
  -- Helper: conjugation on L by any g : G is real-analytic via H3
  have hconj_mdiff : ∀ g : G,
      let α : L →* L :=
        { toFun := fun z => ψ ⟨g⁻¹ * (ψ.symm z : G) * g, by
            have := hG₀_normal.conj_mem (ψ.symm z : G) (ψ.symm z).2 g⁻¹
            simpa [inv_inv] using this⟩
          map_one' := by simp
          map_mul' := fun z₁ z₂ => by
            rw [← map_mul]
            congr 1
            apply Subtype.ext
            simp [mul_assoc] }
      ContMDiff (𝓡 n) (𝓡 n) ω α := by
    intro g α
    refine h3 n L α ?_
    refine ψ.continuous.comp (Continuous.subtype_mk ?_ _)
    exact (continuous_const.mul (continuous_subtype_val.comp ψ.symm.continuous)).mul continuous_const
  -- Prove LieGroup (𝓡 n) ω G for csG
  have hLieG : LieGroup (𝓡 n) ω G := by
    let c₀ := chartAt (EuclideanSpace ℝ (Fin n)) (1 : L)
    have hmulG : ContMDiff ((𝓡 n).prod (𝓡 n)) (𝓡 n) ω (fun p : G × G => p.1 * p.2) := by
      intro ⟨g₁, g₂⟩
      rw [contMDiffAt_iff]
      refine ⟨continuous_mul.continuousAt, ?_⟩
      let α : L →* L :=
        { toFun := fun z => ψ ⟨g₂⁻¹ * (ψ.symm z : G) * g₂, by
            have := hG₀_normal.conj_mem (ψ.symm z : G) (ψ.symm z).2 g₂⁻¹
            simpa [inv_inv] using this⟩
          map_one' := by simp
          map_mul' := fun z₁ z₂ => by
            rw [← map_mul]
            congr 1; apply Subtype.ext; simp [mul_assoc] }
      have hα_mdiff : ContMDiff (𝓡 n) (𝓡 n) ω α := hconj_mdiff g₂
      let F : L × L → L := fun p => α p.1 * p.2
      have hF_mdiff : ContMDiff ((𝓡 n).prod (𝓡 n)) (𝓡 n) ω F :=
        (hα_mdiff.comp contMDiff_fst).mul contMDiff_snd
      have hF_at := (contMDiffAt_iff.mp (hF_mdiff (1, 1))).2
      have hchart_at1 : extChartAt ((𝓡 n).prod (𝓡 n)) (g₁, g₂) (g₁, g₂) =
          extChartAt ((𝓡 n).prod (𝓡 n)) ((1 : L), (1 : L)) (1, 1) := by
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
          (extChartAt (𝓡 n) (1 : L) ∘ F ∘ (extChartAt ((𝓡 n).prod (𝓡 n)) ((1 : L), (1 : L))).symm) := by
        funext ⟨y₁, y₂⟩
        show c₀ (cosetPartialHomeo hG₀_open ψ (g₁ * g₂)
            ((g₁ * (ψ.symm (c₀.symm y₁) : G)) * (g₂ * (ψ.symm (c₀.symm y₂) : G)))) =
          c₀ (α (c₀.symm y₁) * c₀.symm y₂)
        congr 1
        have hconj_mem : g₂⁻¹ * (ψ.symm (c₀.symm y₁) : G) * g₂ ∈ G₀ := by
          have := hG₀_normal.conj_mem (ψ.symm (c₀.symm y₁) : G) (ψ.symm (c₀.symm y₁)).2 g₂⁻¹
          simpa [inv_inv] using this
        have hprod_eq : (g₁ * g₂)⁻¹ * ((g₁ * (ψ.symm (c₀.symm y₁) : G)) * (g₂ * (ψ.symm (c₀.symm y₂) : G))) =
            (g₂⁻¹ * (ψ.symm (c₀.symm y₁) : G) * g₂) * (ψ.symm (c₀.symm y₂) : G) := by
          group
        have hmem : (g₁ * g₂)⁻¹ * ((g₁ * (ψ.symm (c₀.symm y₁) : G)) * (g₂ * (ψ.symm (c₀.symm y₂) : G))) ∈ G₀ := by
          rw [hprod_eq]
          exact G₀.mul_mem hconj_mem (ψ.symm (c₀.symm y₂)).2
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
      let α : L →* L :=
        { toFun := fun z => ψ ⟨(g⁻¹)⁻¹ * (ψ.symm z : G) * g⁻¹, by
            have := hG₀_normal.conj_mem (ψ.symm z : G) (ψ.symm z).2 g
            simpa [inv_inv] using this⟩
          map_one' := by simp
          map_mul' := fun z₁ z₂ => by
            rw [← map_mul]
            congr 1; apply Subtype.ext; simp [mul_assoc] }
      have hα_mdiff : ContMDiff (𝓡 n) (𝓡 n) ω α := hconj_mdiff g⁻¹
      let F : L → L := fun z => α z⁻¹
      have hF_mdiff : ContMDiff (𝓡 n) (𝓡 n) ω F := hα_mdiff.comp (contMDiff_inv (𝓡 n) ω)
      have hF_at := (contMDiffAt_iff.mp (hF_mdiff (1 : L))).2
      have hchart_at1 : extChartAt (𝓡 n) g g = extChartAt (𝓡 n) (1 : L) (1 : L) := by
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
          (extChartAt (𝓡 n) (1 : L) ∘ F ∘ (extChartAt (𝓡 n) (1 : L)).symm) := by
        funext y
        show c₀ (cosetPartialHomeo hG₀_open ψ g⁻¹ (g * (ψ.symm (c₀.symm y) : G))⁻¹) =
          c₀ (α (c₀.symm y)⁻¹)
        congr 1
        have hinv_eq : (g⁻¹)⁻¹ * (g * (ψ.symm (c₀.symm y) : G))⁻¹ =
            (g⁻¹)⁻¹ * (ψ.symm (c₀.symm y)⁻¹ : G) * g⁻¹ := by
          have hsymm_inv : (ψ.symm (c₀.symm y)⁻¹ : G) = (ψ.symm (c₀.symm y) : G)⁻¹ := by
            rw [map_inv]; rfl
          rw [hsymm_inv]
          group
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
    exact
      { contMDiff_mul := hmulG
        contMDiff_inv := hinvG }
  exact ⟨{
    carrier := G
    topologicalSpace := inferInstance
    group := inferInstance
    t2Space := inferInstance
    chartedSpace := csG
    isManifold := hManG
    lieGroup := hLieG
    equiv := ContinuousMulEquiv.refl G
  }⟩

end OMA.R_Hilbert5_hilbert_fifth_problem_R1

end
