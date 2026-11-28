import FormalConjectures.HilbertProblems.«5»
import Mathlib.Algebra.Group.Shrink
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Logic.Small.Basic
import Mathlib.Logic.Small.Set
import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Reduction of `Hilbert5.hilbert_smith_conjecture.variants.riemannian`

Reduces the Hilbert–Smith conjecture for isometric actions on connected smooth Riemannian
manifolds to three independent universe-monomorphic (`Type`) inputs:
1. `H1`: local compact strongly-convex-midpoint balls with stable local distance coordinates,
2. `H2`: unique continuation of Riemannian isometries from nonempty open subsets,
3. `H3`: Gleason–Montgomery–Zippin locally compact Hausdorff NSS theorem.

References:
- S. B. Myers & N. E. Steenrod, "The group of isometries of a Riemannian manifold",
  Ann. of Math. 40 (1939), 400–416.
- A. M. Gleason (1952), D. Montgomery & L. Zippin (1952), L. van den Dries & I. Goldbring (2015).

Thanks to @physbuzz (circumcenter `fixed_center`, `local_nss`, `determining_of_local_distances`)
and @steveDOTdigital & @MechaNuggan (pointwise-topology pullback & Hausdorffness transfer).
Credit: @tkaiman
-/

noncomputable section

open scoped Manifold ContDiff Bundle Topology ENNReal Classical
open Metric Set Filter

namespace OMA.R_Hilbert5_hilbert_smith_conjecture_variants_riemannian_R1

/- ### Part 1: Finiteness of `edist` and universe descent (`Small.{0}`) -/

private lemma edist_ne_top_of_connected {X : Type*} [EMetricSpace X] [ConnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  let S : Set X := {z | edist x z ≠ ⊤}
  have hopen : IsOpen S := by
    rw [EMetric.isOpen_iff]
    intro z hz
    refine ⟨1, zero_lt_one, fun w hw => ?_⟩
    have h1 : edist x w ≤ edist x z + edist z w := edist_triangle x z w
    have h2 : edist z w < 1 := by simpa [Metric.mem_eball, edist_comm] using hw
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hz, ne_top_of_lt h2⟩) h1
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff, EMetric.isOpen_iff]
    intro z hz
    have hzt : edist x z = ⊤ := by simpa [S] using hz
    refine ⟨1, zero_lt_one, fun w hw => ?_⟩
    intro hwt
    have h1 : edist x z ≤ edist x w + edist w z := edist_triangle x w z
    have h2 : edist w z < 1 := by simpa [Metric.mem_eball] using hw
    exact (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hwt, ne_top_of_lt h2⟩) h1) hzt
  have huniv : S = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨x, by simp [S]⟩
  have hy : y ∈ S := by rw [huniv]; trivial
  exact hy

private lemma small_of_countable {α : Type*} [Countable α] : Small.{0} α :=
  small_of_injective (Countable.exists_injective_nat α).choose_spec

private lemma small_of_secondCountable_t2 {α : Type*} [TopologicalSpace α] [T2Space α]
    [SecondCountableTopology α] : Small.{0} α := by
  let b := TopologicalSpace.countableBasis α
  have hb_cnt : b.Countable := TopologicalSpace.countable_countableBasis α
  have hb_basis : TopologicalSpace.IsTopologicalBasis b :=
    TopologicalSpace.isBasis_countableBasis α
  have : Countable b := hb_cnt.to_subtype
  have : Small.{0} b := small_of_countable
  let f : α → Set b := fun x => {u : b | x ∈ u.1}
  have hf : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hopen : IsOpen ({y}ᶜ : Set α) := isClosed_singleton.isOpen_compl
    obtain ⟨u, hub, hxu, huy⟩ := hb_basis.isOpen_iff.mp hopen x hne
    have hmem : (⟨u, hub⟩ : b) ∈ f x := hxu
    rw [hxy] at hmem
    exact huy hmem rfl
  exact small_of_injective hf

private lemma small_of_connected_locally_euclidean {n : ℕ} {X : Type*}
    [EMetricSpace X] [ConnectedSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] :
    Small.{0} X := by
  let P (x : X) (r : ℝ) : Prop :=
    0 ≤ r ∧ r ≤ 1 ∧ SecondCountableTopology (Metric.eball x (ENNReal.ofReal r))
  let rad (x : X) : ℝ := sSup {r : ℝ | P x r}
  have hP_bdd (x : X) : BddAbove {r : ℝ | P x r} := ⟨1, fun r hr => hr.2.1⟩
  have hP_pos (x : X) : ∃ r₀ : ℝ, 0 < r₀ ∧ P x r₀ := by
    have hmem : (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∈ 𝓝 x :=
      chart_source_mem_nhds (EuclideanSpace ℝ (Fin n)) x
    obtain ⟨ε, hε_pos, hε_sub⟩ := EMetric.mem_nhds_iff.mp hmem
    obtain ⟨r, -, hr_pos_e, hr_lt⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε_pos
    have hr_pos : 0 < r := ENNReal.ofReal_pos.mp hr_pos_e
    let r₀ : ℝ := min 1 r
    have hr₀_pos : 0 < r₀ := lt_min zero_lt_one hr_pos
    have hr₀_le1 : r₀ ≤ 1 := min_le_left _ _
    have hsub : Metric.eball x (ENNReal.ofReal r₀) ⊆
        (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
      refine (Metric.eball_subset_eball ?_).trans hε_sub
      exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans hr_lt.le
    let f : Metric.eball x (ENNReal.ofReal r₀) → EuclideanSpace ℝ (Fin n) :=
      fun y => chartAt (EuclideanSpace ℝ (Fin n)) x y.1
    have hf_ind : Topology.IsInducing f := by
      have h1 : Topology.IsInducing
          (fun y : (chartAt (EuclideanSpace ℝ (Fin n)) x).source =>
            chartAt (EuclideanSpace ℝ (Fin n)) x y.1) :=
        ((chartAt (EuclideanSpace ℝ (Fin n)) x).isOpenEmbedding_restrict).isInducing
      have h2 : Topology.IsInducing (Set.inclusion hsub) :=
        (Topology.IsEmbedding.inclusion hsub).isInducing
      exact h1.comp h2
    have hsc : SecondCountableTopology (Metric.eball x (ENNReal.ofReal r₀)) :=
      hf_ind.secondCountableTopology
    exact ⟨r₀, hr₀_pos, hr₀_pos.le, hr₀_le1, hsc⟩
  have hrad_pos (x : X) : 0 < rad x := by
    obtain ⟨r₀, hr₀_pos, hr₀P⟩ := hP_pos x
    exact hr₀_pos.trans_le (le_csSup (hP_bdd x) hr₀P)
  have hP_mono (x : X) {r₁ r₂ : ℝ} (h1 : 0 ≤ r₁) (h12 : r₁ ≤ r₂) (hP2 : P x r₂) : P x r₁ := by
    refine ⟨h1, h12.trans hP2.2.1, ?_⟩
    have hsub : Metric.eball x (ENNReal.ofReal r₁) ⊆ Metric.eball x (ENNReal.ofReal r₂) :=
      Metric.eball_subset_eball (ENNReal.ofReal_le_ofReal h12)
    have : SecondCountableTopology (Metric.eball x (ENNReal.ofReal r₂)) := hP2.2.2
    exact (Topology.IsEmbedding.inclusion hsub).isInducing.secondCountableTopology
  let B (x : X) : Set X := Metric.eball x (ENNReal.ofReal (rad x / 2))
  have hB_sc (x : X) : SecondCountableTopology (B x) := by
    have hlt : rad x / 2 < rad x := half_lt_self (hrad_pos x)
    obtain ⟨r₀, -, hr₀P⟩ := hP_pos x
    obtain ⟨r, hrP, hr_gt⟩ := exists_lt_of_lt_csSup ⟨r₀, hr₀P⟩ hlt
    exact (hP_mono x (by linarith [hrad_pos x]) hr_gt.le hrP).2.2
  have hB_dense (x : X) :
      ∃ D : Set X, D ⊆ B x ∧ D.Countable ∧
        ∀ W : Set X, IsOpen W → (W ∩ B x).Nonempty → (D ∩ W).Nonempty := by
    have : SecondCountableTopology (B x) := hB_sc x
    obtain ⟨t, ht_cnt, ht_dense⟩ := TopologicalSpace.exists_countable_dense (B x)
    refine ⟨Subtype.val '' t, Subtype.coe_image_subset _ _, ht_cnt.image _, ?_⟩
    intro W hW ⟨w, hwW, hwB⟩
    have hW_open : IsOpen (Subtype.val ⁻¹' W : Set (B x)) :=
      hW.preimage continuous_subtype_val
    obtain ⟨⟨z, hzB⟩, hzt, hzW⟩ :=
      ht_dense.exists_mem_open hW_open ⟨⟨w, hwB⟩, hwW⟩
    exact ⟨z, ⟨⟨z, hzB⟩, hzt, rfl⟩, hzW⟩
  choose D hD_sub hD_cnt hD_dense using hB_dense
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  let C : ℕ → Set X := Nat.rec {x₀} (fun _ s => s ∪ ⋃ x ∈ s, D x)
  have hC_cnt (k : ℕ) : (C k).Countable := by
    induction k with
    | zero => exact Set.countable_singleton x₀
    | succ k ih => exact ih.union (ih.biUnion fun x _ => hD_cnt x)
  let Cinf : Set X := ⋃ k : ℕ, C k
  have hCinf_cnt : Cinf.Countable := Set.countable_iUnion hC_cnt
  let U : Set X := ⋃ x ∈ Cinf, B x
  have hU_open : IsOpen U :=
    isOpen_biUnion fun x _ => Metric.isOpen_eball
  have hU_ne : U.Nonempty := by
    refine ⟨x₀, Set.mem_biUnion (Set.mem_iUnion.mpr ⟨0, Set.mem_singleton x₀⟩) ?_⟩
    exact Metric.mem_eball_self (ENNReal.ofReal_pos.mpr (half_pos (hrad_pos x₀)))
  have hU_closed : IsClosed U := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    let W : Set X := Metric.eball y (ENNReal.ofReal (rad y / 4))
    have hW_open : IsOpen W := Metric.isOpen_eball
    have hyW : y ∈ W :=
      Metric.mem_eball_self (ENNReal.ofReal_pos.mpr (by linarith [hrad_pos y]))
    obtain ⟨u, huW, huU⟩ := mem_closure_iff.mp hy W hW_open hyW
    obtain ⟨x, hxCinf, huBx⟩ := Set.mem_iUnion₂.mp huU
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxCinf
    obtain ⟨z, hzDx, hzW⟩ := hD_dense x W hW_open ⟨u, huW, huBx⟩
    have hzCinf : z ∈ Cinf := by
      refine Set.mem_iUnion.mpr ⟨k + 1, Or.inr ?_⟩
      exact Set.mem_biUnion hxk hzDx
    have hzy : edist z y < ENNReal.ofReal (rad y / 4) := Metric.mem_eball.mp hzW
    have hlt34 : 3 * rad y / 4 < rad y := by linarith [hrad_pos y]
    obtain ⟨r₀, -, hr₀P⟩ := hP_pos y
    obtain ⟨r, hrP, hr_gt⟩ := exists_lt_of_lt_csSup ⟨r₀, hr₀P⟩ hlt34
    let r' : ℝ := r - rad y / 4
    have hr'_gt : rad y / 2 < r' := by dsimp [r']; linarith
    have hr'_pos : 0 < r' := by linarith [hrad_pos y]
    have hr'_le1 : r' ≤ 1 := by dsimp [r']; linarith [hrP.2.1, hrad_pos y]
    have hball_sub : Metric.eball z (ENNReal.ofReal r') ⊆ Metric.eball y (ENNReal.ofReal r) := by
      intro w hw
      have hwz : edist w z < ENNReal.ofReal r' := Metric.mem_eball.mp hw
      have htri : edist w y ≤ edist w z + edist z y := edist_triangle w z y
      have hsum : edist w z + edist z y < ENNReal.ofReal r' + ENNReal.ofReal (rad y / 4) :=
        ENNReal.add_lt_add hwz hzy
      have heq : ENNReal.ofReal r' + ENNReal.ofReal (rad y / 4) = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_add hr'_pos.le (by linarith [hrad_pos y])]
        congr 1; dsimp [r']; ring
      rw [heq] at hsum
      exact lt_of_le_of_lt htri hsum
    have hPz : P z r' := by
      refine ⟨hr'_pos.le, hr'_le1, ?_⟩
      have : SecondCountableTopology (Metric.eball y (ENNReal.ofReal r)) := hrP.2.2
      exact (Topology.IsEmbedding.inclusion hball_sub).isInducing.secondCountableTopology
    have hrad_z : r' ≤ rad z := le_csSup (hP_bdd z) hPz
    have hyBz : y ∈ B z := by
      have h1 : edist y z < ENNReal.ofReal (rad y / 4) := by rwa [edist_comm]
      have h2 : ENNReal.ofReal (rad y / 4) < ENNReal.ofReal (rad z / 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (half_pos (hrad_pos z))).mpr (by linarith)
      exact lt_trans h1 h2
    exact Set.mem_biUnion hzCinf hyBz
  have hU_univ : U = Set.univ := IsClopen.eq_univ ⟨hU_closed, hU_open⟩ hU_ne
  have : Countable Cinf := hCinf_cnt.to_subtype
  have hCinf_small : Small.{0} Cinf := small_of_countable
  have hB_small : ∀ x : X, x ∈ Cinf → Small.{0} (B x) := by
    intro x _
    have : SecondCountableTopology (B x) := hB_sc x
    exact small_of_secondCountable_t2
  have hU_small : Small.{0} U :=
    @small_biUnion.{0} _ _ Cinf hCinf_small (fun x _ => B x) hB_small
  rw [hU_univ] at hU_small
  exact small_of_surjective (f := fun x : (Set.univ : Set X) => x.1)
    (fun x => ⟨⟨x, Set.mem_univ x⟩, rfl⟩)

/- ### Part 2: Transporting charts, smooth manifolds, and Riemannian structures along a homeomorphism -/

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

private lemma homeomorphChartedSpace_mfderiv_coe {n : ℕ}
    {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    (e : X' ≃ₜ X) (x' : X') :
    let _ := homeomorphChartedSpace (H := EuclideanSpace ℝ (Fin n)) e
    mfderiv (𝓡 n) (𝓡 n) e x' = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  intro cs
  have hmd : MDifferentiableAt (𝓡 n) (𝓡 n) e x' :=
    (homeomorphChartedSpace_contMDiff_coe (k := ∞) e x').mdifferentiableAt (by simp)
  simp only [mfderiv, hmd, ↓reduceIte]
  have hpt : extChartAt (𝓡 n) x' x' = chartAt (EuclideanSpace ℝ (Fin n)) (e x') (e x') := rfl
  have htarget : (chartAt (EuclideanSpace ℝ (Fin n)) (e x')).target ∈
      𝓝 (extChartAt (𝓡 n) x' x') := by
    rw [hpt]
    exact (chartAt (EuclideanSpace ℝ (Fin n)) (e x')).open_target.mem_nhds (mem_chart_target _ _)
  have hev : writtenInExtChartAt (𝓡 n) (𝓡 n) x' e =ᶠ[𝓝 (extChartAt (𝓡 n) x' x')] id := by
    filter_upwards [htarget] with y hy
    change (chartAt (EuclideanSpace ℝ (Fin n)) (e x'))
      (e (e.symm ((chartAt (EuclideanSpace ℝ (Fin n)) (e x')).symm y))) = y
    simp [(chartAt (EuclideanSpace ℝ (Fin n)) (e x')).right_inv hy]
  rw [show Set.range (𝓡 n) = Set.univ by simp, fderivWithin_univ]
  rw [hev.fderiv_eq, fderiv_id]

private lemma homeomorphChartedSpace_mfderiv_symm {n : ℕ}
    {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    (e : X' ≃ₜ X) (x : X) :
    let _ := homeomorphChartedSpace (H := EuclideanSpace ℝ (Fin n)) e
    mfderiv (𝓡 n) (𝓡 n) e.symm x = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  intro cs
  have hmd : MDifferentiableAt (𝓡 n) (𝓡 n) e.symm x :=
    (homeomorphChartedSpace_contMDiff_symm (k := ∞) e x).mdifferentiableAt (by simp)
  simp only [mfderiv, hmd, ↓reduceIte]
  have hpt : extChartAt (𝓡 n) x x = chartAt (EuclideanSpace ℝ (Fin n)) x x := rfl
  have htarget : (chartAt (EuclideanSpace ℝ (Fin n)) x).target ∈
      𝓝 (extChartAt (𝓡 n) x x) := by
    rw [hpt]
    exact (chartAt (EuclideanSpace ℝ (Fin n)) x).open_target.mem_nhds (mem_chart_target _ _)
  have hev : writtenInExtChartAt (𝓡 n) (𝓡 n) x e.symm =ᶠ[𝓝 (extChartAt (𝓡 n) x x)] id := by
    filter_upwards [htarget] with y hy
    change (chartAt (EuclideanSpace ℝ (Fin n)) (e (e.symm x)))
      (e (e.symm ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm y))) = y
    simp [(chartAt (EuclideanSpace ℝ (Fin n)) x).right_inv hy]
  rw [show Set.range (𝓡 n) = Set.univ by simp, fderivWithin_univ]
  rw [hev.fderiv_eq, fderiv_id]

private abbrev homeomorphRiemannianMetric {n : ℕ} {X X' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [hRB : Bundle.RiemannianBundle (fun x : X => TangentSpace (𝓡 n) x)]
    (e : X' ≃ₜ X) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) X' := homeomorphChartedSpace e
    Bundle.RiemannianMetric (fun x' : X' => TangentSpace (𝓡 n) x') :=
  { inner := fun x' => hRB.g.inner (e x')
    symm := fun x' => hRB.g.symm (e x')
    pos := fun x' => hRB.g.pos (e x')
    continuousAt := fun x' => hRB.g.continuousAt (e x')
    isVonNBounded := fun x' => hRB.g.isVonNBounded (e x') }

private lemma homeomorph_symmL_eq {n : ℕ} {X X' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]
    (e : X' ≃ₜ X) (x₀' x' : X') (v : EuclideanSpace ℝ (Fin n)) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) X' := homeomorphChartedSpace e
    let _ : IsManifold (𝓡 n) ∞ X' := homeomorphChartedSpace_isManifold e
    ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀').symmL ℝ x' v :
      EuclideanSpace ℝ (Fin n)) =
    ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (e x₀')).symmL ℝ (e x') v :
      EuclideanSpace ℝ (Fin n)) := by
  intro csX' hMan'
  have hchart_src :
      x' ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀').source ↔
        e x' ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (e x₀')).source := by
    change x' ∈ (e.toOpenPartialHomeomorph.trans
      (chartAt (EuclideanSpace ℝ (Fin n)) (e x₀'))).source ↔ _
    simp only [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Set.mem_inter_iff, Set.mem_univ, Set.mem_preimage, true_and]
    rfl
  by_cases hx : x' ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀').source
  · have hxe : e x' ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (e x₀')).source := hchart_src.mp hx
    have hL : ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀').symmL
        ℝ x' v : EuclideanSpace ℝ (Fin n)) =
        fderivWithin ℝ ((chartAt (EuclideanSpace ℝ (Fin n)) x').extend (𝓡 n) ∘
          ((chartAt (EuclideanSpace ℝ (Fin n)) x₀').extend (𝓡 n)).symm)
          (Set.range (𝓡 n)) ((chartAt (EuclideanSpace ℝ (Fin n)) x₀').extend (𝓡 n) x') v := by
      rw [TangentBundle.symmL_trivializationAt_eq_core hx]; rfl
    have hR : ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (e x₀')).symmL
        ℝ (e x') v : EuclideanSpace ℝ (Fin n)) =
        fderivWithin ℝ ((chartAt (EuclideanSpace ℝ (Fin n)) (e x')).extend (𝓡 n) ∘
          ((chartAt (EuclideanSpace ℝ (Fin n)) (e x₀')).extend (𝓡 n)).symm)
          (Set.range (𝓡 n)) ((chartAt (EuclideanSpace ℝ (Fin n)) (e x₀')).extend (𝓡 n) (e x')) v := by
      rw [TangentBundle.symmL_trivializationAt_eq_core hxe]; rfl
    rw [hL, hR]
    have hcomp : ((chartAt (EuclideanSpace ℝ (Fin n)) x').extend (𝓡 n) ∘
        ((chartAt (EuclideanSpace ℝ (Fin n)) x₀').extend (𝓡 n)).symm) =
        ((chartAt (EuclideanSpace ℝ (Fin n)) (e x')).extend (𝓡 n) ∘
        ((chartAt (EuclideanSpace ℝ (Fin n)) (e x₀')).extend (𝓡 n)).symm) := by
      funext y
      change (chartAt (EuclideanSpace ℝ (Fin n)) (e x'))
        (e (e.symm ((chartAt (EuclideanSpace ℝ (Fin n)) (e x₀')).symm y))) =
        (chartAt (EuclideanSpace ℝ (Fin n)) (e x'))
        ((chartAt (EuclideanSpace ℝ (Fin n)) (e x₀')).symm y)
      simp
    have hpt : (chartAt (EuclideanSpace ℝ (Fin n)) x₀').extend (𝓡 n) x' =
        (chartAt (EuclideanSpace ℝ (Fin n)) (e x₀')).extend (𝓡 n) (e x') := rfl
    rw [hcomp, hpt]
  · have hxe : e x' ∉ (chartAt (EuclideanSpace ℝ (Fin n)) (e x₀')).source := mt hchart_src.mpr hx
    have hL : ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀').symmL
        ℝ x' v : EuclideanSpace ℝ (Fin n)) = 0 :=
      Bundle.Trivialization.symmL_apply_of_notMem _ (by simpa using hx) v
    have hR : ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (e x₀')).symmL
        ℝ (e x') v : EuclideanSpace ℝ (Fin n)) = 0 :=
      Bundle.Trivialization.symmL_apply_of_notMem _ (by simpa using hxe) v
    exact hL.trans hR.symm

private lemma homeomorph_isContMDiffRiemannianBundle {n : ℕ} {X X' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]
    [hRB : Bundle.RiemannianBundle (fun x : X => TangentSpace (𝓡 n) x)]
    [hCRB : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : X => TangentSpace (𝓡 n) x)]
    (e : X' ≃ₜ X) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) X' := homeomorphChartedSpace e
    let _ : IsManifold (𝓡 n) ∞ X' := homeomorphChartedSpace_isManifold e
    let _ : Bundle.RiemannianBundle (fun x' : X' => TangentSpace (𝓡 n) x') :=
      ⟨homeomorphRiemannianMetric (n := n) e⟩
    IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x' : X' => TangentSpace (𝓡 n) x') := by
  intro csX' hMan' instRB'
  obtain ⟨gX, hgX_mdiff, hgX_inner⟩ := hCRB.exists_contMDiff
  refine ⟨fun x' => gX (e x'), ?_, fun x' v w => hgX_inner (e x') v w⟩
  intro x₀'
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hX := (contMDiffAt_hom_bundle _ (x₀ := e x₀')).mp (hgX_mdiff (e x₀'))
  have hcomp := hX.2.comp x₀' (homeomorphChartedSpace_contMDiff_coe (k := ∞) e x₀')
  refine hcomp.congr_of_eventuallyEq ?_
  let T' := trivializationAt (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (fun b => TangentSpace (𝓡 n) b →L[ℝ] ℝ) x₀'
  let T := trivializationAt (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (fun b => TangentSpace (𝓡 n) b →L[ℝ] ℝ) (e x₀')
  filter_upwards [chart_source_mem_nhds (EuclideanSpace ℝ (Fin n)) x₀'] with x' hx
  have hxe : e x' ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (e x₀')).source := by
    change x' ∈ (e.toOpenPartialHomeomorph.trans
      (chartAt (EuclideanSpace ℝ (Fin n)) (e x₀'))).source at hx
    simpa [OpenPartialHomeomorph.trans_source] using hx
  have hbx : x' ∈ T'.baseSet := by
    change x' ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀').source ∩ Set.univ
    exact ⟨hx, trivial⟩
  have hbxe : e x' ∈ T.baseSet := by
    change e x' ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (e x₀')).source ∩ Set.univ
    exact ⟨hxe, trivial⟩
  ext v w
  let φ' : TangentSpace (𝓡 n) x' →L[ℝ] ℝ :=
    (gX (e x')) ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀').symmL
      ℝ x' v)
  let φ : TangentSpace (𝓡 n) (e x') →L[ℝ] ℝ :=
    (gX (e x')) ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (e x₀')).symmL
      ℝ (e x') v)
  change (T'.continuousLinearMapAt ℝ x' φ') w = (T.continuousLinearMapAt ℝ (e x') φ) w
  have hL : (T'.continuousLinearMapAt ℝ x' φ') w =
      φ' ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀').symmL
        ℝ x' w) := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hbx]
    change (ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) ℝ (Bundle.Trivial X' ℝ) x₀' x' x₀' x' φ') w = _
    simp [ContinuousLinearMap.inCoordinates]
  have hR : (T.continuousLinearMapAt ℝ (e x') φ) w =
      φ ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (e x₀')).symmL
        ℝ (e x') w) := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hbxe]
    change (ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) ℝ (Bundle.Trivial X ℝ) (e x₀') (e x') (e x₀') (e x') φ) w = _
    simp [ContinuousLinearMap.inCoordinates]
  rw [hL, hR]
  exact congrArg₂ (fun a b : EuclideanSpace ℝ (Fin n) => gX (e x') a b)
    (homeomorph_symmL_eq e x₀' x' v) (homeomorph_symmL_eq e x₀' x' w)

private lemma homeomorph_isRiemannianManifold {n : ℕ} {X X' : Type*}
    [EMetricSpace X] [EMetricSpace X']
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [hRB : Bundle.RiemannianBundle (fun x : X => TangentSpace (𝓡 n) x)]
    [hRM : IsRiemannianManifold (𝓡 n) X]
    (e : X' ≃ₜ X) (he_iso : Isometry e) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) X' := homeomorphChartedSpace e
    let _ : Bundle.RiemannianBundle (fun x' : X' => TangentSpace (𝓡 n) x') :=
      ⟨homeomorphRiemannianMetric (n := n) e⟩
    IsRiemannianManifold (𝓡 n) X' := by
  intro csX' instRB'
  refine ⟨fun x' y' => ?_⟩
  have hed : edist x' y' = Manifold.riemannianEDist (𝓡 n) (e x') (e y') := by
    rw [← he_iso x' y', hRM.out (e x') (e y')]
  rw [hed]
  have he_mdiff : ContMDiff (𝓡 n) (𝓡 n) 1 e :=
    homeomorphChartedSpace_contMDiff_coe (k := 1) e
  have hes_mdiff : ContMDiff (𝓡 n) (𝓡 n) 1 e.symm :=
    homeomorphChartedSpace_contMDiff_symm (k := 1) e
  have hnorm_eq : ∀ (z' : X') (v : EuclideanSpace ℝ (Fin n)),
      @enorm (TangentSpace (𝓡 n) z') _ v = @enorm (TangentSpace (𝓡 n) (e z')) _ v := by
    intro z' v
    rfl
  apply le_antisymm
  · conv_rhs => rw [Manifold.riemannianEDist]
    rw [le_iInf₂_iff]
    intro γ' hγ'
    let γ : Path (e x') (e y') := γ'.map e.continuous
    have hγ : ContMDiff (𝓡∂ 1) (𝓡 n) 1 γ := he_mdiff.comp hγ'
    have hle : Manifold.riemannianEDist (𝓡 n) (e x') (e y') ≤
        ∫⁻ t, ‖mfderiv (𝓡∂ 1) (𝓡 n) γ t 1‖ₑ := by
      rw [Manifold.riemannianEDist]; exact biInf_le _ hγ
    refine hle.trans_eq ?_
    congr 1; funext t
    have hmd_e : MDifferentiableAt (𝓡 n) (𝓡 n) e (γ' t) :=
      he_mdiff.mdifferentiable one_ne_zero (γ' t)
    have hmd_γ' : MDifferentiableAt (𝓡∂ 1) (𝓡 n) γ' t :=
      hγ'.mdifferentiable one_ne_zero t
    have hchain : mfderiv (𝓡∂ 1) (𝓡 n) γ t =
        (mfderiv (𝓡 n) (𝓡 n) e (γ' t)).comp (mfderiv (𝓡∂ 1) (𝓡 n) γ' t) :=
      mfderiv_comp t hmd_e hmd_γ'
    rw [hchain, homeomorphChartedSpace_mfderiv_coe e (γ' t)]
    exact (hnorm_eq (γ' t) _).symm
  · conv_rhs => rw [Manifold.riemannianEDist]
    rw [le_iInf₂_iff]
    intro γ hγ
    let γ' : Path x' y' :=
      (γ.map e.symm.continuous).cast
        (e.symm_apply_apply x').symm (e.symm_apply_apply y').symm
    have hγ' : ContMDiff (𝓡∂ 1) (𝓡 n) 1 γ' := hes_mdiff.comp hγ
    have hle : Manifold.riemannianEDist (𝓡 n) x' y' ≤
        ∫⁻ t, ‖mfderiv (𝓡∂ 1) (𝓡 n) γ' t 1‖ₑ := by
      rw [Manifold.riemannianEDist]; exact biInf_le _ hγ'
    refine hle.trans_eq ?_
    congr 1; funext t
    have hmd_es : MDifferentiableAt (𝓡 n) (𝓡 n) e.symm (γ t) :=
      hes_mdiff.mdifferentiable one_ne_zero (γ t)
    have hmd_γ : MDifferentiableAt (𝓡∂ 1) (𝓡 n) γ t :=
      hγ.mdifferentiable one_ne_zero t
    have hchain : mfderiv (𝓡∂ 1) (𝓡 n) γ' t =
        (mfderiv (𝓡 n) (𝓡 n) e.symm (γ t)).comp (mfderiv (𝓡∂ 1) (𝓡 n) γ t) :=
      mfderiv_comp t hmd_es hmd_γ
    rw [hchain, homeomorphChartedSpace_mfderiv_symm e (γ t)]
    let v : EuclideanSpace ℝ (Fin n) := mfderiv (𝓡∂ 1) (𝓡 n) γ t 1
    have h1 : @enorm (TangentSpace (𝓡 n) (γ' t)) _ v =
        @enorm (TangentSpace (𝓡 n) (e (γ' t))) _ v := rfl
    have h2 : ∀ z₁ z₂ : X, z₁ = z₂ →
        @enorm (TangentSpace (𝓡 n) z₁) _ v = @enorm (TangentSpace (𝓡 n) z₂) _ v := by
      rintro z _ rfl; rfl
    exact h1.trans (h2 (e (γ' t)) (γ t) (e.apply_symm_apply (γ t)))

/- ### Part 3: Circumcenter, local NSS, and landmark determination (after @physbuzz) -/

private lemma fixed_center {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
    (iso : ∀ g : G, Isometry (g • · : X → X)) (p : X) (R : ℝ)
    (compact : IsCompact (Metric.closedBall p R))
    (bounded : ∀ g : G, dist p (g • p) ≤ R)
    (coef : ℝ) (positive : 0 < coef)
    (mid : ∀ x ∈ Metric.closedBall p R, ∀ y ∈ Metric.closedBall p R, ∃ m : X, ∀ g : G,
      (dist m (g • p)) ^ 2 ≤ ((dist x (g • p)) ^ 2 + (dist y (g • p)) ^ 2) / 2 -
        coef * (dist x y) ^ 2) :
    ∃ c ∈ Metric.closedBall p R, ∀ g : G, g • c = c := by
  let r (x : X) := ⨆ g : G, dist x (g • p)
  have rbd (x : X) : BddAbove (Set.range fun g : G => dist x (g • p)) := by
    refine ⟨dist x p + R, ?_⟩
    rintro _ ⟨g, rfl⟩
    exact (dist_triangle ..).trans (add_le_add_right (bounded g) _)
  have term (x : X) (g : G) : dist x (g • p) ≤ r x := le_ciSup (rbd x) g
  have distp (x : X) : dist x p ≤ r x := by simpa using term x 1
  have nonneg (x : X) : 0 ≤ r x := (dist_nonneg (x := x) (y := p)).trans (distp x)
  have triangle (x y : X) : r x ≤ dist x y + r y := by
    apply ciSup_le; intro g
    exact (dist_triangle ..).trans (add_le_add_right (term y g) _)
  have lips : LipschitzWith 1 r := by
    apply LipschitzWith.of_dist_le_mul; intro x y
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_le_iff]
    have h := triangle x y; have k := triangle y x; rw [dist_comm y x] at k
    constructor <;> linarith
  have pR : r p ≤ R := ciSup_le bounded
  have pp : p ∈ Metric.closedBall p R := mem_closedBall.mpr (by simpa using bounded 1)
  obtain ⟨c, hc, opt⟩ := compact.exists_isMinOn ⟨p, pp⟩ lips.continuous.continuousOn
  have rmin : r c ≤ R := (opt pp).trans pR
  have global_min (x : X) : r c ≤ r x := by
    by_cases inball : x ∈ Metric.closedBall p R
    · exact opt inball
    · exact rmin.trans ((le_of_lt (lt_of_not_ge inball)).trans (distp x))
  have invle (g : G) (x : X) : r (g • x) ≤ r x := by
    apply ciSup_le; intro k
    have eq : k • p = g • ((g⁻¹ * k) • p) := by simp [mul_smul]
    rw [eq, (iso g).dist_eq]; exact term x _
  have uniq (y : X) (hy : r y = r c) : y = c := by
    have yb : y ∈ Metric.closedBall p R := mem_closedBall.mpr ((distp y).trans (hy ▸ rmin))
    obtain ⟨m, hm⟩ := mid c hc y yb
    let z := (r c) ^ 2 - coef * (dist c y) ^ 2
    have lim (g : G) : dist m (g • p) ^ 2 ≤ z := by
      have x := sq_le_sq' (by linarith [nonneg c, dist_nonneg (x := c) (y := g • p)]) (term c g)
      have y' := sq_le_sq' (by linarith [nonneg y, dist_nonneg (x := y) (y := g • p)]) (term y g)
      rw [hy] at y'
      dsimp [z]; linarith [hm g]
    have zz : 0 ≤ z := (sq_nonneg _).trans (lim 1)
    have rm : r m ≤ Real.sqrt z := ciSup_le fun g => Real.le_sqrt_of_sq_le (lim g)
    have minimal := mul_self_le_mul_self (nonneg c) ((global_min m).trans rm)
    have root := Real.sq_sqrt zz
    have d : dist c y = 0 := by
      by_contra ne
      have str := mul_pos positive (sq_pos_of_ne_zero ne)
      dsimp [z] at root str
      nlinarith
    exact (dist_eq_zero.mp d).symm
  exact ⟨c, hc, fun g => uniq _ (le_antisymm (invle g c) (global_min _))⟩

private lemma determining_of_local_distances {X I : Type*} [MetricSpace X] (c : I → X) (i₀ : I)
    (δ : ℝ) (dp : 0 < δ)
    (coords : Set.InjOn (fun x : X => fun i : I => dist x (c i)) (Metric.ball (c i₀) δ))
    (extend_id : ∀ e : Equiv.Perm X, Isometry (e : X → X) →
      (∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, e x = x) → e = 1)
    (e : Equiv.Perm X) (iso : Isometry (e : X → X)) (fixed : ∀ i, e (c i) = c i) : e = 1 := by
  apply extend_id e iso
  refine ⟨Metric.ball (c i₀) δ, isOpen_ball, ⟨c i₀, mem_ball_self dp⟩, ?_⟩
  intro x hx
  have invariant (i : I) : dist (e x) (c i) = dist x (c i) := by
    rw [← fixed i]; simpa only [fixed] using iso.dist_eq x (c i)
  exact coords (mem_ball.mpr ((invariant i₀).trans_lt (mem_ball.mp hx))) hx (funext invariant)

private lemma local_nss {X I : Type*} [MetricSpace X] [Fintype I] (p : I → X)
    (R coef : I → ℝ) (pos : ∀ i, 0 < R i) (strong : ∀ i, 0 < coef i)
    (compact : ∀ i, IsCompact (Metric.closedBall (p i) (R i)))
    (mid : ∀ i, ∀ x ∈ Metric.closedBall (p i) (R i), ∀ y ∈ Metric.closedBall (p i) (R i),
      ∃ m : X, ∀ z ∈ Metric.closedBall (p i) (R i),
        (dist m z) ^ 2 ≤ ((dist x z) ^ 2 + (dist y z) ^ 2) / 2 - coef i * (dist x y) ^ 2)
    (det : ∀ c : I → X, (∀ i, c i ∈ Metric.closedBall (p i) (R i)) →
      ∀ e : Equiv.Perm X, Isometry (e : X → X) → (∀ i, e (c i) = c i) → e = 1) :
    ∃ U : Set (X → X), IsOpen U ∧ id ∈ U ∧
      ∀ K : Subgroup (Equiv.Perm X), (∀ e ∈ K, Isometry (e : X → X)) →
        (∀ e ∈ K, (e : X → X) ∈ U) → K = ⊥ := by
  let U : Set (X → X) := ⋂ i, (fun f : X → X => f (p i)) ⁻¹' Metric.ball (p i) (R i)
  have op : IsOpen U :=
    isOpen_iInter_of_finite fun i => isOpen_ball.preimage (continuous_apply (p i))
  refine ⟨U, op, mem_iInter.mpr fun i => mem_ball_self (pos i), ?_⟩
  intro K iso all
  have bounded (i : I) (e : K) : dist (p i) (e • p i) ≤ R i := by
    have v := mem_iInter.mp (all e.val e.property) i
    change dist (e • p i) (p i) < R i at v
    rw [dist_comm]; exact v.le
  have centers (i : I) : ∃ c ∈ Metric.closedBall (p i) (R i), ∀ e : K, e • c = c :=
    fixed_center (fun e => iso e.val e.property) (p i) (R i) (compact i) (bounded i)
      (coef i) (strong i) (by
        intro x hx y hy
        obtain ⟨m, hm⟩ := mid i x hx y hy
        exact ⟨m, fun e => hm (e • p i) (mem_closedBall.mpr (by rw [dist_comm]; exact bounded i e))⟩)
  choose c near fixed using centers
  apply le_antisymm _ bot_le
  intro e he
  exact Subgroup.mem_bot.mpr (det c near e (iso e he) fun i => fixed i (⟨e, he⟩ : K))

/- ### Part 4: Lifting `AdmitsLieGroupStructure` across `ContinuousMulEquiv` -/

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
      funext ⟨a, b⟩
      simp [Prod.map]
    rw [heq]
    exact hψs.comp ((contMDiff_mul (I := 𝓡 m) (n := ω)).comp (hψ.prodMap hψ))
  have hinv : ContMDiff (𝓡 m) (𝓡 m) ω (fun a : G => a⁻¹) := by
    have heq : (fun a : G => a⁻¹) = (ψ.symm ∘ (fun z : L => z⁻¹) ∘ ψ) := by
      funext a
      simp
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

/- ### Part 5: Hypotheses and main reduction theorem -/

/-- **Local Riemannian geometry (compact strongly-convex-midpoint balls & stable distance
coordinates, in `Type`)**:
every connected smooth `n`-dimensional Riemannian manifold admits finitely many landmarks
`p : Fin (k + 1) → X` with positive radii `R i`, convexity constants `c i`, and `δ > 0`
such that each closed ball `closedBall (p i) (R i)` is compact and satisfies the local
squared-distance midpoint inequality, and for any perturbed landmarks `q i ∈ closedBall (p i) (R i)`,
the distance-to-landmarks map `x ↦ (dist x (q i))_i` is injective on `ball (q 0) δ`. -/
def H1 : Prop :=
  ∀ (n : ℕ) (X : Type) [MetricSpace X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]
    [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (𝓡 n) x)]
    [IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : X ↦ TangentSpace (𝓡 n) x)]
    [IsRiemannianManifold (𝓡 n) X],
    ∃ (k : ℕ) (p : Fin (k + 1) → X) (R c : Fin (k + 1) → ℝ) (δ : ℝ),
      (∀ i, 0 < R i) ∧ (∀ i, 0 < c i) ∧ 0 < δ ∧
      (∀ i, IsCompact (Metric.closedBall (p i) (R i))) ∧
      (∀ i, ∀ x ∈ Metric.closedBall (p i) (R i), ∀ y ∈ Metric.closedBall (p i) (R i),
        ∃ m : X, ∀ z ∈ Metric.closedBall (p i) (R i),
          (dist m z) ^ 2 ≤ ((dist x z) ^ 2 + (dist y z) ^ 2) / 2 - c i * (dist x y) ^ 2) ∧
      (∀ q : Fin (k + 1) → X, (∀ i, q i ∈ Metric.closedBall (p i) (R i)) →
        Set.InjOn (fun x : X ↦ fun i : Fin (k + 1) ↦ dist x (q i)) (Metric.ball (q 0) δ))

/-- **Unique continuation of Riemannian isometries (in `Type`)**:
a bijective isometry of a connected smooth Riemannian manifold that fixes every point of a
nonempty open subset is the identity. -/
def H2 : Prop :=
  ∀ (n : ℕ) (X : Type) [MetricSpace X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]
    [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (𝓡 n) x)]
    [IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : X ↦ TangentSpace (𝓡 n) x)]
    [IsRiemannianManifold (𝓡 n) X],
    ∀ e : Equiv.Perm X, Isometry (e : X → X) →
      (∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, e x = x) → e = 1

/-- **Gleason–Montgomery–Zippin theorem (in `Type`)**:
every locally compact Hausdorff topological group with no small subgroups admits a Lie group
structure. -/
def H3 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G],
    (∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
      ∀ H : Subgroup G, (H : Set G) ⊆ V → H = ⊥) →
    AdmitsLieGroupStructure G

theorem main : H1 → H2 → H3 →
    type_of% @Hilbert5.hilbert_smith_conjecture.variants.riemannian := by
  intro h1 h2 h3 G _ _ n X hEM hConn hCS hMan hRB hCRB hRM hTG hLC hAct hCSmul hFaith hiso
  -- Step 1: Upgrade connected EMetricSpace X to MetricSpace X (same edist and topology)
  have hfin : ∀ x y : X, edist x y ≠ ⊤ := edist_ne_top_of_connected
  let instMS_X : MetricSpace X := EMetricSpace.toMetricSpace hfin
  -- Step 2: Universe descent Small.{0} X and Small.{0} G
  have hSmallX : Small.{0} X := small_of_connected_locally_euclidean (n := n)
  let actX (g : G) (x : X) : X := g • x
  have hactX_inj : Function.Injective actX := fun g₁ g₂ h =>
    eq_of_smul_eq_smul (congrFun h)
  have hSmallG : Small.{0} G := small_of_injective hactX_inj
  -- Step 3: Build MetricSpace X' := Shrink.{0} X : Type and obtain pointwise NSS via H1, H2
  let X' : Type := Shrink.{0} X
  let e : X' ≃ X := (equivShrink X).symm
  let instMS' : MetricSpace X' := @MetricSpace.induced X' X e e.injective instMS_X
  have he_iso : Isometry e := fun x y => rfl
  let e_hom : X' ≃ₜ X :=
    { toEquiv := e
      continuous_toFun := he_iso.continuous
      continuous_invFun := by
        have hinv : Isometry e.symm := fun x y => by
          change edist (e (e.symm x)) (e (e.symm y)) = edist x y
          simp
        exact hinv.continuous }
  have hNSS_X' : ∃ U : Set (X' → X'), IsOpen U ∧ id ∈ U ∧
      ∀ K : Subgroup (Equiv.Perm X'), (∀ f ∈ K, Isometry (f : X' → X')) →
        (∀ f ∈ K, (f : X' → X') ∈ U) → K = ⊥ := by
    have hConn' : ConnectedSpace X' :=
      connectedSpace_iff_univ.mpr <| by
        simpa [Set.image_univ, e_hom.symm.range_coe] using
          isConnected_univ.image e_hom.symm e_hom.symm.continuous.continuousOn
    let csX' : ChartedSpace (EuclideanSpace ℝ (Fin n)) X' := homeomorphChartedSpace e_hom
    have hMan' : IsManifold (𝓡 n) ∞ X' := homeomorphChartedSpace_isManifold e_hom
    let instRB' : Bundle.RiemannianBundle (fun x' : X' => TangentSpace (𝓡 n) x') :=
      ⟨homeomorphRiemannianMetric (n := n) e_hom⟩
    have hCRB' : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
        (fun x' : X' => TangentSpace (𝓡 n) x') :=
      homeomorph_isContMDiffRiemannianBundle (n := n) e_hom
    have hRM' : IsRiemannianManifold (𝓡 n) X' :=
      homeomorph_isRiemannianManifold (n := n) e_hom he_iso
    obtain ⟨k, p, R, coef, δ, hR, hc, hδ, hcomp, hmid, hcoords⟩ := h1 n X'
    have hdet : ∀ c : Fin (k + 1) → X', (∀ i, c i ∈ Metric.closedBall (p i) (R i)) →
        ∀ f : Equiv.Perm X', Isometry (f : X' → X') → (∀ i, f (c i) = c i) → f = 1 :=
      fun c hc_mem =>
        determining_of_local_distances c 0 δ hδ (hcoords c hc_mem) (h2 n X')
    exact local_nss p R coef hR hc hcomp hmid hdet
  -- Step 4: Transport G to G' := Shrink.{0} G : Type with faithful isometric action on X'
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
  have hiso' : ∀ g' : G', Isometry (g' • · : X' → X') := by
    intro g' x₁' x₂'
    change edist (e (e.symm ((φ g') • (e x₁')))) (e (e.symm ((φ g') • (e x₂')))) =
      edist (e x₁') (e x₂')
    simp [hiso (φ g') (e x₁') (e x₂')]
  -- Step 5: Pull back U along the continuous faithful action G' → (X' → X') (after @steveDOTdigital)
  obtain ⟨U, hU_open, hidU, hU_nss⟩ := hNSS_X'
  let ρ : G' →* Equiv.Perm X' := MulAction.toPermHom G' X'
  let act (g' : G') (x' : X') : X' := g' • x'
  have hact_cont : Continuous act := continuous_pi fun x' => continuous_id.smul continuous_const
  have hact_inj : Function.Injective act := fun g₁ g₂ h => eq_of_smul_eq_smul (congrFun h)
  have hT2' : T2Space G' := T2Space.of_injective_continuous hact_inj hact_cont
  have hLieG' : AdmitsLieGroupStructure G' := by
    apply h3 G'
    refine ⟨act ⁻¹' U, hU_open.preimage hact_cont, ?_, ?_⟩
    · have h1act : act (1 : G') = id := funext fun x' => one_smul G' x'
      change act (1 : G') ∈ U
      rwa [h1act]
    · intro K hK
      have hmap : K.map ρ = ⊥ := by
        apply hU_nss
        · rintro _ ⟨g', _, rfl⟩
          exact hiso' g'
        · rintro _ ⟨g', hg', rfl⟩
          exact hK hg'
      apply le_antisymm _ bot_le
      intro g' hg'
      have hmem : ρ g' ∈ K.map ρ := ⟨g', hg', rfl⟩
      rw [hmap] at hmem
      have heq : ρ g' = 1 := Subgroup.mem_bot.mp hmem
      apply MulAction.toPerm_injective (β := X')
      change ρ g' = ρ 1
      simpa only [map_one] using heq
  -- Step 7: Lift AdmitsLieGroupStructure G' back to G : Type u
  exact admitsLieGroupStructure_of_continuousMulEquiv φ hLieG'

end OMA.R_Hilbert5_hilbert_smith_conjecture_variants_riemannian_R1
