import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R2
import Mathlib

/-!
# Brown's two-open-cells theorem

Adapted from Will (Ziang) Li's `Poincare-High-Dim` at cffda864. Original module
names and copyright notices are retained. The sources have been combined for
the one-file submission. The Lean 4.33.1 port supplies a closed-graph lemma,
updates conditional-reduction lemma names and removes two tactic registrations.
The Apache 2.0 license is reproduced at the end.
-/

private theorem continuous_from_closed_graph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] {f : X → Y} (hgraph : IsClosed f.graph) :
    Continuous f := by
  rw [continuous_iff_isClosed]
  intro F hF
  have he : f ⁻¹' F = Prod.fst '' (f.graph ∩ (Prod.snd ⁻¹' F)) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, f x), ⟨rfl, hx⟩, rfl⟩
    · rintro ⟨⟨x,y⟩, ⟨he, hy⟩, rfl⟩
      change f x = y at he
      exact he.symm ▸ hy
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ (hgraph.inter (hF.preimage continuous_snd))

/- Source module Submission.Topology.Cellular.CellularQuotient -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# Identifying spaces obtained by collapsing the same set

Two quotient maps with the same fibers have homeomorphic targets. In particular, a
continuous surjection from a compact space that collapses exactly a subset `K` has the
same target, up to homeomorphism, as any other such surjection. This is the quotient step
in Brown's cellular shrinking argument.
-/

namespace PoincareHighDim

open Set Topology

/-- A map identifies all points of `K`, and makes no other identifications. -/
def CollapsesExactly {X Y : Type*} (f : X → Y) (K : Set X) : Prop :=
  ∀ x y, f x = f y ↔ x = y ∨ x ∈ K ∧ y ∈ K

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Quotient maps with the same fibers identify their target spaces homeomorphically. -/
noncomputable def quotientHomeomorphOfSameFibers {f : X → Y} {g : X → Z}
    (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (h : ∀ x y, f x = f y ↔ g x = g y) : Y ≃ₜ Z :=
  (hf.homeomorph (f := ⟨f, hf.continuous⟩)).symm.trans
    ((Homeomorph.Quotient.congrRight h).trans (hg.homeomorph (f := ⟨g, hg.continuous⟩)))

theorem quotientHomeomorphOfSameFibers_apply {f : X → Y} {g : X → Z}
    (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (h : ∀ x y, f x = f y ↔ g x = g y) (x : X) :
    quotientHomeomorphOfSameFibers hf hg h (f x) = g x := by
  change (hg.homeomorph (f := ⟨g, hg.continuous⟩)) ((Homeomorph.Quotient.congrRight h)
    ((hf.homeomorph (f := ⟨f, hf.continuous⟩)).symm (f x))) = g x
  have hx : (hf.homeomorph (f := ⟨f, hf.continuous⟩)) (Quotient.mk (Setoid.ker f) x) = f x := rfl
  rw [← hx, Homeomorph.symm_apply_apply]
  rfl

/-- The compact Hausdorff version requires only continuous surjections. -/
noncomputable def homeomorphOfSameFibers [CompactSpace X] [T2Space Y] [T2Space Z]
    {f : X → Y} {g : X → Z} (hf : Continuous f) (hfs : Function.Surjective f)
    (hg : Continuous g) (hgs : Function.Surjective g)
    (h : ∀ x y, f x = f y ↔ g x = g y) : Y ≃ₜ Z :=
  quotientHomeomorphOfSameFibers (IsQuotientMap.of_surjective_continuous hfs hf)
    (IsQuotientMap.of_surjective_continuous hgs hg) h

/-- Collapsing precisely the same subset produces homeomorphic target spaces. -/
theorem nonempty_homeomorph_of_collapsesExactly [CompactSpace X] [T2Space Y] [T2Space Z]
    {f : X → Y} {g : X → Z} {K : Set X}
    (hf : Continuous f) (hfs : Function.Surjective f)
    (hg : Continuous g) (hgs : Function.Surjective g)
    (hfK : CollapsesExactly f K) (hgK : CollapsesExactly g K) : Nonempty (Y ≃ₜ Z) :=
  ⟨homeomorphOfSameFibers hf hfs hg hgs (fun x y => (hfK x y).trans (hgK x y).symm)⟩

end PoincareHighDim

end

/- Source module Submission.Topology.Schoenflies.OpenEmbeddingCollapse -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# Collapsing the complement of an open embedding

An open embedding into a Hausdorff space defines a continuous map to the one-point
compactification of its domain: use the inverse chart inside its range and send every
other point to infinity.
-/

namespace PoincareHighDim

open Set Topology
open scoped OnePoint

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]

/-- Collapse the complement of a proper open embedding to the point at infinity. -/
theorem exists_collapse_of_openEmbedding {φ : Y → X} (hφ : IsOpenEmbedding φ)
    (hproper : range φ ≠ univ) :
    ∃ f : C(X, OnePoint Y), Function.Surjective f ∧
      CollapsesExactly f (range φ)ᶜ ∧
      (∀ y, f (φ y) = (y : OnePoint Y)) ∧
      (∀ x ∉ range φ, f x = ∞) := by
  classical
  let e : Y ≃ₜ range φ := hφ.isEmbedding.toHomeomorph
  let f : X → OnePoint Y := fun x => if hx : x ∈ range φ then e.symm ⟨x, hx⟩ else ∞
  have hfin (y : Y) : f (φ y) = (y : OnePoint Y) := by
    rw [show f (φ y) = (e.symm ⟨φ y, mem_range_self y⟩ : OnePoint Y) from
      dif_pos (mem_range_self y)]
    exact congrArg (fun z : Y => (z : OnePoint Y)) (e.symm_apply_apply y)
  have hout (x : X) (hx : x ∉ range φ) : f x = ∞ := dif_neg hx
  have hcont : Continuous f := by
    apply continuous_def.mpr
    intro U hU
    by_cases hinfty : (∞ : OnePoint Y) ∈ U
    · have heq : f ⁻¹' U = (φ '' (((↑) : Y → OnePoint Y) ⁻¹' U)ᶜ)ᶜ := by
        ext x
        by_cases hx : x ∈ range φ
        · obtain ⟨y, rfl⟩ := hx
          simp only [mem_preimage, hfin, mem_compl_iff,
            hφ.injective.mem_set_image]
          exact not_not.symm
        · simp only [mem_preimage, hout x hx, hinfty, true_iff, mem_compl_iff]
          exact fun hi => hx ((image_subset_range _ _) hi)
      rw [heq]
      exact (((OnePoint.isOpen_def.mp hU).1 hinfty).image hφ.continuous).isClosed.isOpen_compl
    · have heq : f ⁻¹' U = φ '' (((↑) : Y → OnePoint Y) ⁻¹' U) := by
        ext x
        by_cases hx : x ∈ range φ
        · obtain ⟨y, rfl⟩ := hx
          simp only [mem_preimage, hfin, hφ.injective.mem_set_image]
        · simp only [mem_preimage, hout x hx, hinfty, false_iff]
          exact fun hi => hx ((image_subset_range _ _) hi)
      rw [heq]
      exact hφ.isOpenMap _ (OnePoint.isOpen_def.mp hU).2
  have hfiber : CollapsesExactly f (range φ)ᶜ := by
    intro x y
    by_cases hx : x ∈ range φ
    · obtain ⟨u, rfl⟩ := hx
      by_cases hy : y ∈ range φ
      · obtain ⟨v, rfl⟩ := hy
        simp only [hfin, OnePoint.coe_eq_coe, mem_compl_iff, mem_range_self, not_true_eq_false,
          and_self, or_false]
        exact hφ.injective.eq_iff.symm
      · simp only [hfin, hout y hy, OnePoint.coe_ne_infty, mem_compl_iff, mem_range_self,
          not_true_eq_false, false_and, or_false, false_iff]
        exact fun h => hy (h ▸ mem_range_self u)
    · by_cases hy : y ∈ range φ
      · obtain ⟨v, rfl⟩ := hy
        simp only [hout x hx, hfin, OnePoint.infty_ne_coe, mem_compl_iff, mem_range_self,
          not_true_eq_false, and_false, or_false, false_iff]
        exact fun h => hx (h.symm ▸ mem_range_self v)
      · simp [hout x hx, hout y hy, hx, hy]
  refine ⟨⟨f, hcont⟩, ?_, hfiber, hfin, hout⟩
  intro z
  induction z using OnePoint.rec with
  | infty =>
      obtain ⟨x, hx⟩ := nonempty_compl.mpr hproper
      exact ⟨x, hout x hx⟩
  | coe y => exact ⟨φ y, hfin y⟩

end PoincareHighDim

end

/- Source module Submission.Topology.Disks.Disk -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# The closed unit disk

`Disk n` is the closed unit ball of `EuclideanSpace ℝ (Fin n)` viewed as a topological space,
`diskSphere n` its boundary sphere and `diskInterior n` its interior, both as subsets of the disk.
-/

namespace PoincareHighDim

open Metric

/-- The closed unit disk `Dⁿ ⊆ ℝⁿ`. -/
abbrev Disk (n : ℕ) : Type := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The boundary sphere `Sⁿ⁻¹ ⊆ Dⁿ`. -/
def diskSphere (n : ℕ) : Set (Disk n) := Subtype.val ⁻¹' sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The open unit ball `Dⁿ \ Sⁿ⁻¹ ⊆ Dⁿ`. -/
def diskInterior (n : ℕ) : Set (Disk n) := Subtype.val ⁻¹' ball (0 : EuclideanSpace ℝ (Fin n)) 1

theorem mem_diskSphere {n : ℕ} {x : Disk n} :
    x ∈ diskSphere n ↔ ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  simp [diskSphere]

theorem mem_diskInterior {n : ℕ} {x : Disk n} :
    x ∈ diskInterior n ↔ ‖(x : EuclideanSpace ℝ (Fin n))‖ < 1 := by
  simp [diskInterior]

theorem diskSphere_union_diskInterior (n : ℕ) : diskSphere n ∪ diskInterior n = Set.univ := by
  ext x
  simp only [Set.mem_union, mem_diskSphere, mem_diskInterior, Set.mem_univ, iff_true]
  have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := mem_closedBall_zero_iff.1 x.2
  rcases lt_or_eq_of_le hx with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem disjoint_diskSphere_diskInterior (n : ℕ) : Disjoint (diskSphere n) (diskInterior n) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_diskSphere] at hx
  rw [mem_diskInterior] at hx'
  exact absurd hx (ne_of_lt hx')

theorem isClosed_diskSphere (n : ℕ) : IsClosed (diskSphere n) :=
  isClosed_sphere.preimage continuous_subtype_val

theorem isOpen_diskInterior (n : ℕ) : IsOpen (diskInterior n) :=
  isOpen_ball.preimage continuous_subtype_val

/-- The boundary sphere of the disk is homeomorphic to the unit sphere. -/
noncomputable def diskSphereHomeomorph (n : ℕ) :
    diskSphere n ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (by rw [Subtype.range_coe]; exact sphere_subset_closedBall)

end PoincareHighDim

end

/- Source module Submission.Topology.Cellular.Cellular -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# Closed cells for cellular shrinking

A closed cell is an embedded closed disk whose open disk has open image. Recording the
openness explicitly makes the elementary shrinking arguments independent of invariance
of domain. A cellular set is the intersection of a nested sequence of these cells.
-/

namespace PoincareHighDim

open Set Metric Topology

/-- An embedded closed disk with open interior image. -/
structure ClosedCell (n : ℕ) (X : Type*) [TopologicalSpace X] where
  map : Disk n → X
  isClosedEmbedding : IsClosedEmbedding map
  isOpen_interior : IsOpen (map '' diskInterior n)

namespace ClosedCell

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

/-- The closed image of a cell. -/
def carrier (c : ClosedCell n X) : Set X := range c.map

/-- The specified open disk inside a cell. -/
def interiorSet (c : ClosedCell n X) : Set X := c.map '' diskInterior n

theorem isClosed_carrier (c : ClosedCell n X) : IsClosed c.carrier :=
  c.isClosedEmbedding.isClosed_range

theorem isCompact_carrier (c : ClosedCell n X) : IsCompact c.carrier := by
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  exact isCompact_range c.isClosedEmbedding.continuous

theorem interiorSet_subset_carrier (c : ClosedCell n X) : c.interiorSet ⊆ c.carrier :=
  image_subset_range _ _

theorem interiorSet_subset_interior (c : ClosedCell n X) : c.interiorSet ⊆ interior c.carrier :=
  interior_maximal c.interiorSet_subset_carrier c.isOpen_interior

theorem carrier_sdiff_interiorSet (c : ClosedCell n X) :
    c.carrier \ c.interiorSet = c.map '' diskSphere n := by
  ext x
  constructor
  · rintro ⟨⟨v, rfl⟩, hv⟩
    refine ⟨v, ?_, rfl⟩
    have hnot : v ∉ diskInterior n := fun h => hv ⟨v, h, rfl⟩
    have hall : v ∈ diskSphere n ∪ diskInterior n := by
      rw [diskSphere_union_diskInterior]
      trivial
    exact hall.resolve_right hnot
  · rintro ⟨v, hv, rfl⟩
    refine ⟨mem_range_self v, ?_⟩
    intro hi
    rw [interiorSet, c.isClosedEmbedding.injective.mem_set_image] at hi
    exact Set.disjoint_left.1 (disjoint_diskSphere_diskInterior n) hv hi

theorem frontier_carrier_subset (c : ClosedCell n X) :
    frontier c.carrier ⊆ c.map '' diskSphere n := by
  rw [frontier, c.isClosed_carrier.closure_eq, ← c.carrier_sdiff_interiorSet]
  exact sdiff_subset_sdiff_right c.interiorSet_subset_interior

theorem interiorSet_nonempty (c : ClosedCell n X) : c.interiorSet.Nonempty := by
  let z : Disk n := ⟨0, mem_closedBall_self zero_le_one⟩
  exact ⟨c.map z, z, mem_diskInterior.mpr (by simp [z]), rfl⟩

theorem carrier_nonempty (c : ClosedCell n X) : c.carrier.Nonempty :=
  c.interiorSet_nonempty.mono c.interiorSet_subset_carrier

/-- A compact subset of the open cell lies inside a smaller concentric closed disk. -/
theorem exists_radius_of_isCompact [T2Space X] (c : ClosedCell n X) {K : Set X}
    (hK : IsCompact K) (hKC : K ⊆ c.interiorSet) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧
      ∀ x : Disk n, c.map x ∈ K → ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ R := by
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hc : IsCompact (c.map ⁻¹' K) :=
    (hK.isClosed.preimage c.isClosedEmbedding.continuous).isCompact
  rcases (c.map ⁻¹' K).eq_empty_or_nonempty with he | hne
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro x hx
    have : x ∈ c.map ⁻¹' K := hx
    simp only [he, mem_empty_iff_false] at this
  · obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn hne continuous_subtype_val.norm.continuousOn
    have hx1 : ‖(x : EuclideanSpace ℝ (Fin n))‖ < 1 := by
      have hi := hKC hx
      rw [interiorSet, c.isClosedEmbedding.injective.mem_set_image] at hi
      exact mem_diskInterior.mp hi
    refine ⟨(‖(x : EuclideanSpace ℝ (Fin n))‖ + 1) / 2, by positivity, by linarith, ?_⟩
    intro y hy
    have hle : ‖(y : EuclideanSpace ℝ (Fin n))‖ ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖ := hmax hy
    linarith

end ClosedCell

/-- A cellular set is an intersection of closed cells nested in their open interiors. -/
def IsCellular {X : Type*} [TopologicalSpace X] (n : ℕ) (K : Set X) : Prop :=
  ∃ c : ℕ → ClosedCell n X,
    (∀ i, (c (i + 1)).carrier ⊆ (c i).interiorSet) ∧ K = ⋂ i, (c i).carrier

/-- A closed nonempty set with arbitrarily small cell neighborhoods is cellular. -/
theorem isCellular_of_cell_neighborhoods {X : Type*} [MetricSpace X] {n : ℕ} {K : Set X}
    (hclosed : IsClosed K) (hne : K.Nonempty)
    (hcell : ∀ U : Set X, IsOpen U → K ⊆ U →
      ∃ c : ClosedCell n X, K ⊆ c.interiorSet ∧ c.carrier ⊆ U) : IsCellular n K := by
  classical
  obtain ⟨c₀, hc₀, -⟩ := hcell univ isOpen_univ (subset_univ _)
  let C := {c : ClosedCell n X // K ⊆ c.interiorSet}
  have hnext (i : ℕ) (c : C) : ∃ d : C,
      d.1.carrier ⊆ c.1.interiorSet ∩ {x | infDist x K < 1 / ((i : ℝ) + 1)} := by
    obtain ⟨d, hdK, hd⟩ := hcell
      (c.1.interiorSet ∩ {x | infDist x K < 1 / ((i : ℝ) + 1)})
      (c.1.isOpen_interior.inter (isOpen_lt (continuous_infDist_pt K) continuous_const))
      (by
        intro x hx
        refine ⟨c.2 hx, ?_⟩
        change infDist x K < 1 / ((i : ℝ) + 1)
        rw [infDist_zero_of_mem hx]
        positivity)
    exact ⟨⟨d, hdK⟩, hd⟩
  let step (i : ℕ) (c : C) : C := Classical.choose (hnext i c)
  let seq : ℕ → C := fun i => Nat.rec ⟨c₀, hc₀⟩ step i
  have hstep (i : ℕ) : (seq (i + 1)).1.carrier ⊆
      (seq i).1.interiorSet ∩ {x | infDist x K < 1 / ((i : ℝ) + 1)} :=
    Classical.choose_spec (hnext i (seq i))
  refine ⟨fun i => (seq i).1, fun i => (hstep i).trans inter_subset_left, ?_⟩
  ext x
  constructor
  · intro hx
    exact mem_iInter.mpr fun i => (seq i).1.interiorSet_subset_carrier ((seq i).2 hx)
  · intro hx
    apply (hclosed.mem_iff_infDist_zero hne).mpr
    apply le_antisymm _ infDist_nonneg
    apply ge_of_tendsto (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact Filter.Eventually.of_forall fun i =>
      ((hstep i (mem_iInter.mp hx (i + 1))).2).le

end PoincareHighDim

end

/- Source module Submission.Topology.Spheres.SphereSimplyConnected -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# Spheres of dimension at least two are simply connected

We prove that the unit sphere `Sᵏ ⊆ ℝᵏ⁺¹` is simply connected for `k ≥ 2`
(`PoincareHighDim.simplyConnectedSpace_sphere_of_two_le`).

## Proof outline

Let `S` be the unit sphere of a real inner product space `E` and let `γ` be a loop in `S`.

1. (`exists_subdivision`) By uniform continuity of `γ`, there is `n ≥ 1` such that on each piece
   `[i/n, (i+1)/n]` the loop stays in the open hemisphere `{y | ⟪y, γ(i/n)⟫ > 0}`.
2. (`polygon`, `exists_homotopic_piecewise_geodesic`) Let `L` be the polygonal path in `E`
   through the sample points `γ(i/n)`, traversed at uniform speed. On the `i`-th piece both
   `γ` and `L` lie in the `i`-th open hemisphere, so the straight-line homotopy between them never
   passes through `0`; composing it with the radial projection `v ↦ ‖v‖⁻¹ • v` yields a homotopy
   in `S`, relative to the endpoints, from `γ` to the "piecewise geodesic" loop
   `δ = radialProj ∘ L`.
3. (`exists_sphere_notMem_span_pair`) The loop `δ` takes values in the finite union of the planes
   `span {γ(i/n), γ((i+1)/n)}`. If `dim E ≥ 3` these are proper closed subspaces, hence a finite
   union of them has empty interior and misses some point `q` of `S`.
4. (`isSimplyConnected_sphere_compl_singleton`) `S ∖ {q}` is homeomorphic to `ℝᵏ` via stereographic
   projection, hence contractible, hence simply connected; so `δ` is null-homotopic in `S ∖ {q}`,
   and therefore in `S`.

Together with path-connectedness of the sphere (`isPathConnected_sphere`) this gives simple
connectivity via `simply_connected_iff_loops_nullhomotopic`.
-/

namespace PoincareHighDim

open Metric Module Set unitInterval

noncomputable section

/-! ### Clamping to the unit interval -/

/-- The clamp of a real number to `[0, 1]`. -/
def clamp01 (r : ℝ) : ℝ := max 0 (min r 1)

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clamp01_of_nonpos {r : ℝ} (h : r ≤ 0) : clamp01 r = 0 := by
  unfold clamp01
  rw [max_eq_left]
  exact (min_le_left _ _).trans h

theorem clamp01_of_one_le {r : ℝ} (h : 1 ≤ r) : clamp01 r = 1 := by
  unfold clamp01
  rw [min_eq_right h, max_eq_right zero_le_one]

theorem clamp01_of_mem {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : clamp01 r = r := by
  unfold clamp01
  rw [min_eq_left h1, max_eq_right h0]

/-! ### Elementary real-number facts -/

/-- A convex combination of two positive numbers is positive. -/
theorem convex_pos {a b θ : ℝ} (ha : 0 < a) (hb : 0 < b) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    0 < (1 - θ) * a + θ * b := by
  rcases eq_or_lt_of_le h1 with rfl | hlt
  · simpa
  · have h2 : 0 < (1 - θ) * a := mul_pos (by linarith) ha
    have h3 : 0 ≤ θ * b := mul_nonneg h0 hb.le
    linarith

/-- Each `s ∈ [0, 1]` lies in one of the `n` pieces `[i/n, (i+1)/n]`, `i < n`. -/
theorem exists_piece {n : ℕ} (hn : 0 < n) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ∃ i < n, (i : ℝ) / n ≤ s ∧ s ≤ (i + 1) / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rcases eq_or_lt_of_le h1 with rfl | hlt
  · refine ⟨n - 1, Nat.sub_lt hn one_pos, ?_, ?_⟩
    · rw [div_le_one hn']
      exact_mod_cast Nat.sub_le n 1
    · rw [le_div_iff₀ hn', one_mul]
      have : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        rw [← Nat.cast_succ]
        congr 1
        omega
      linarith
  · refine ⟨⌊n * s⌋₊, ?_, ?_, ?_⟩
    · rw [Nat.floor_lt (by positivity)]
      nlinarith
    · rw [div_le_iff₀ hn', mul_comm]
      exact Nat.floor_le (by positivity)
    · rw [le_div_iff₀ hn', mul_comm]
      exact (Nat.lt_floor_add_one _).le

/-! ### Radial projection and inner products -/

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two unit vectors at distance less than `1` have positive inner product. -/
theorem inner_pos_of_norm_sub_lt_one {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : ‖u - v‖ < 1) : 0 < inner ℝ u v := by
  have h1 := norm_sub_sq_real u v
  rw [hu, hv] at h1
  have h2 : ‖u - v‖ ^ 2 < 1 := by nlinarith [norm_nonneg (u - v)]
  linarith

/-- The radial projection `v ↦ ‖v‖⁻¹ • v` of `E ∖ {0}` onto the unit sphere. -/
def radialProj (v : E) : E := ‖v‖⁻¹ • v

theorem norm_radialProj {v : E} (hv : v ≠ 0) : ‖radialProj v‖ = 1 := by
  simpa [radialProj] using norm_smul_inv_norm (𝕜 := ℝ) hv

theorem radialProj_mem_sphere {v : E} (hv : v ≠ 0) : radialProj v ∈ sphere (0 : E) 1 :=
  mem_sphere_zero_iff_norm.2 (norm_radialProj hv)

theorem radialProj_of_norm_eq_one {v : E} (hv : ‖v‖ = 1) : radialProj v = v := by
  simp [radialProj, hv]

theorem continuous_radialProj_comp {X : Type*} [TopologicalSpace X] {f : X → E}
    (hf : Continuous f) (h : ∀ x, f x ≠ 0) : Continuous fun x => radialProj (f x) :=
  ((continuous_norm.comp hf).inv₀ fun x => norm_ne_zero_iff.mpr (h x)).smul hf

theorem radialProj_mem_span {W : Submodule ℝ E} {v : E} (h : v ∈ W) : radialProj v ∈ W :=
  W.smul_mem _ h

theorem mem_span_of_radialProj_mem {W : Submodule ℝ E} {v : E} (hv : v ≠ 0)
    (h : radialProj v ∈ W) : v ∈ W := by
  have := W.smul_mem ‖v‖ h
  rwa [radialProj, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul] at this

/-! ### Polygonal paths -/

/-- The polygonal path through `p 0, p 1, …, p n`, traversed at uniform speed: on the piece
`[i/n, (i+1)/n]` it is the affine segment from `p i` to `p (i+1)`. -/
def polygon (p : ℕ → E) (n : ℕ) (s : ℝ) : E :=
  p 0 + ∑ j ∈ Finset.range n, clamp01 (n * s - j) • (p (j + 1) - p j)

theorem continuous_polygon (p : ℕ → E) (n : ℕ) : Continuous (polygon p n) := by
  unfold polygon
  refine continuous_const.add (continuous_finsetSum _ fun j _ => ?_)
  exact (continuous_clamp01.comp (by fun_prop)).smul continuous_const

theorem polygon_zero (p : ℕ → E) (n : ℕ) : polygon p n 0 = p 0 := by
  unfold polygon
  rw [Finset.sum_eq_zero, add_zero]
  intro j _
  rw [clamp01_of_nonpos (by simp), zero_smul]

theorem polygon_one (p : ℕ → E) (n : ℕ) : polygon p n 1 = p n := by
  unfold polygon
  have h : ∀ j ∈ Finset.range n, clamp01 (n * 1 - j) • (p (j + 1) - p j) = p (j + 1) - p j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    rw [clamp01_of_one_le (by linarith), one_smul]
  rw [Finset.sum_congr rfl h, Finset.sum_range_sub]
  abel

/-- On the `i`-th piece, the polygonal path is the affine segment from `p i` to `p (i+1)`. -/
theorem polygon_eq_of_mem (p : ℕ → E) {n i : ℕ} (hi : i < n) {s : ℝ} (hs : (i : ℝ) / n ≤ s)
    (hs' : s ≤ (i + 1) / n) :
    polygon p n s = p i + (n * s - i) • (p (i + 1) - p i) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le i) hi)
  have hs1 : (i : ℝ) ≤ n * s := by rwa [div_le_iff₀ hn', mul_comm] at hs
  have hs2 : n * s ≤ (i : ℝ) + 1 := by rwa [le_div_iff₀ hn', mul_comm] at hs'
  unfold polygon
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hi), Finset.sum_range_succ]
  have h1 : ∀ j ∈ Finset.range i, clamp01 (n * s - j) • (p (j + 1) - p j) = p (j + 1) - p j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj' : (j : ℝ) + 1 ≤ i := by exact_mod_cast hj
    rw [clamp01_of_one_le (by linarith), one_smul]
  have h2 : ∀ j ∈ Finset.Ico (i + 1) n, clamp01 (n * s - j) • (p (j + 1) - p j) = 0 := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hj' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hj.1
    rw [clamp01_of_nonpos (by linarith), zero_smul]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_range_sub,
    Finset.sum_const_zero, add_zero, clamp01_of_mem (by linarith) (by linarith)]
  abel

theorem polygon_mem_span (p : ℕ → E) {n i : ℕ} (hi : i < n) {s : ℝ} (hs : (i : ℝ) / n ≤ s)
    (hs' : s ≤ (i + 1) / n) :
    polygon p n s ∈ Submodule.span ℝ {p i, p (i + 1)} := by
  rw [polygon_eq_of_mem p hi hs hs', Submodule.mem_span_pair]
  refine ⟨1 - (n * s - i), n * s - i, ?_⟩
  rw [sub_smul, one_smul, smul_sub]
  abel

theorem inner_polygon_pos (p : ℕ → E) {n i : ℕ} (hi : i < n) {s : ℝ} (hs : (i : ℝ) / n ≤ s)
    (hs' : s ≤ (i + 1) / n) {v : E} (h1 : 0 < inner ℝ (p i) v) (h2 : 0 < inner ℝ (p (i + 1)) v) :
    0 < inner ℝ (polygon p n s) v := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le i) hi)
  have hs1 : (i : ℝ) ≤ n * s := by rwa [div_le_iff₀ hn', mul_comm] at hs
  have hs2 : n * s ≤ (i : ℝ) + 1 := by rwa [le_div_iff₀ hn', mul_comm] at hs'
  rw [polygon_eq_of_mem p hi hs hs', inner_add_left, real_inner_smul_left, inner_sub_left]
  have key := convex_pos h1 h2 (by linarith : 0 ≤ n * s - i) (by linarith : n * s - i ≤ 1)
  have : inner ℝ (p i) v + (n * s - i) * (inner ℝ (p (i + 1)) v - inner ℝ (p i) v)
      = (1 - (n * s - i)) * inner ℝ (p i) v + (n * s - i) * inner ℝ (p (i + 1)) v := by ring
  rw [this]
  exact key

/-! ### Subdividing a loop in the sphere -/

/-- A loop in the unit sphere admits a uniform subdivision such that on each piece
`[i/n, (i+1)/n]` it stays in the open hemisphere centered at the sample point `γ (i/n)`. -/
theorem exists_subdivision {x : sphere (0 : E) 1} (γ : Path x x) :
    ∃ n : ℕ, 0 < n ∧ ∀ i < n, ∀ s : I, (i : ℝ) / n ≤ s → (s : ℝ) ≤ (i + 1) / n →
      0 < inner ℝ (γ s : E) (γ.extend ((i : ℝ) / n) : E) := by
  have hc : Continuous fun s : I => (γ s : E) := continuous_subtype_val.comp γ.continuous
  have hu := CompactSpace.uniformContinuous_of_continuous hc
  rw [Metric.uniformContinuous_iff] at hu
  obtain ⟨ε, hε, hεu⟩ := hu 1 one_pos
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  refine ⟨m + 1, Nat.succ_pos m, fun i hi s hs hs' => ?_⟩
  have hn' : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos m)
  have hin : (i : ℝ) / ((m + 1 : ℕ) : ℝ) ∈ I := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
    rw [div_le_one hn']
    exact_mod_cast hi.le
  rw [Path.extend_extends' γ ⟨_, hin⟩]
  apply inner_pos_of_norm_sub_lt_one (norm_eq_of_mem_sphere _) (norm_eq_of_mem_sphere _)
  have key := @hεu s ⟨_, hin⟩ ?_
  · rwa [dist_eq_norm] at key
  · rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
    have h1 : (s : ℝ) - (i : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 / ((m : ℝ) + 1) := by
      have : ((i : ℝ) + 1) / ((m + 1 : ℕ) : ℝ) - (i : ℝ) / ((m + 1 : ℕ) : ℝ)
          = 1 / ((m : ℝ) + 1) := by
        rw [← sub_div, add_sub_cancel_left, Nat.cast_succ]
      linarith
    constructor <;> linarith

/-! ### Replacing a loop by a piecewise geodesic loop -/

/-- Every loop in the unit sphere is homotopic (relative to the base point) to a "piecewise
geodesic" loop `δ`, whose values lie in finitely many planes `span {p i, p (i+1)}`. -/
theorem exists_homotopic_piecewise_geodesic {x : sphere (0 : E) 1} (γ : Path x x) :
    ∃ (n : ℕ) (p : ℕ → E) (δ : Path x x), γ.Homotopic δ ∧
      ∀ s : I, ∃ i < n, (δ s : E) ∈ Submodule.span ℝ {p i, p (i + 1)} := by
  obtain ⟨n, hn, hsub⟩ := exists_subdivision γ
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set p : ℕ → E := fun j => (γ.extend ((j : ℝ) / n) : E) with hp
  have hp_norm : ∀ j, ‖p j‖ = 1 := fun j => norm_eq_of_mem_sphere _
  have hp0 : p 0 = x := by simp [hp]
  have hpn : p n = x := by simp [hp, div_self hn'.ne']
  -- the straight-line interpolation between `γ` and the polygonal path never vanishes
  have hpos : ∀ (t : I) (s : I),
      ∃ i < n, 0 < inner ℝ ((1 - (t : ℝ)) • (γ s : E) + (t : ℝ) • polygon p n s) (p i) := by
    intro t s
    obtain ⟨i, hi, hs, hs'⟩ := exists_piece hn s.2.1 s.2.2
    refine ⟨i, hi, ?_⟩
    have h1 : 0 < inner ℝ (γ s : E) (p i) := hsub i hi s hs hs'
    have h2 : 0 < inner ℝ (polygon p n s) (p i) := by
      apply inner_polygon_pos p hi hs hs'
      · rw [real_inner_self_eq_norm_sq, hp_norm]
        norm_num
      · have hmem : ((i : ℝ) + 1) / n ∈ I := by
          refine ⟨by positivity, ?_⟩
          rw [div_le_one hn']
          exact_mod_cast hi
        have h3 := hsub i hi ⟨_, hmem⟩
          (div_le_div_of_nonneg_right (by linarith) hn'.le) le_rfl
        convert h3 using 2
        simp only [hp, Nat.cast_add, Nat.cast_one]
        exact congrArg Subtype.val (Path.extend_extends' γ ⟨_, hmem⟩)
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    exact convex_pos h1 h2 t.2.1 t.2.2
  set w : I × I → E := fun ts => (1 - (ts.1 : ℝ)) • (γ ts.2 : E) + (ts.1 : ℝ) • polygon p n ts.2
    with hw_def
  have hw : ∀ ts, w ts ≠ 0 := fun ts h => by
    obtain ⟨i, -, hi⟩ := hpos ts.1 ts.2
    rw [show (1 - (ts.1 : ℝ)) • (γ ts.2 : E) + (ts.1 : ℝ) • polygon p n ts.2 = w ts from rfl, h,
      inner_zero_left] at hi
    exact lt_irrefl _ hi
  have hwc : Continuous w := by
    apply Continuous.add
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp (γ.continuous.comp continuous_snd))
    · exact (continuous_subtype_val.comp continuous_fst).smul
        ((continuous_polygon p n).comp (continuous_subtype_val.comp continuous_snd))
  have hw0 : ∀ s : I, w (0, s) = (γ s : E) := fun s => by simp [hw_def]
  have hw1 : ∀ s : I, w (1, s) = polygon p n s := fun s => by simp [hw_def]
  have hwt0 : ∀ t : I, w (t, 0) = (x : E) := fun t => by
    simp only [hw_def, Set.Icc.coe_zero, polygon_zero, hp0, Path.source]
    rw [← add_smul, sub_add_cancel, one_smul]
  have hwt1 : ∀ t : I, w (t, 1) = (x : E) := fun t => by
    simp only [hw_def, Set.Icc.coe_one, polygon_one, hpn, Path.target]
    rw [← add_smul, sub_add_cancel, one_smul]
  -- the homotopy in the sphere
  set H : I × I → E := fun ts => radialProj (w ts) with hH_def
  have hH1 : ∀ ts, ‖H ts‖ = 1 := fun ts => norm_radialProj (hw ts)
  have hHc : Continuous H := continuous_radialProj_comp hwc hw
  have hHx : ‖(x : E)‖ = 1 := norm_eq_of_mem_sphere x
  have hHt0 : ∀ t : I, H (t, 0) = (x : E) := fun t => by
    change radialProj (w (t, 0)) = (x : E)
    rw [hwt0, radialProj_of_norm_eq_one hHx]
  have hHt1 : ∀ t : I, H (t, 1) = (x : E) := fun t => by
    change radialProj (w (t, 1)) = (x : E)
    rw [hwt1, radialProj_of_norm_eq_one hHx]
  have hH0 : ∀ s : I, H (0, s) = (γ s : E) := fun s => by
    change radialProj (w (0, s)) = (γ s : E)
    rw [hw0, radialProj_of_norm_eq_one (norm_eq_of_mem_sphere (γ s))]
  let δ : Path x x :=
    { toFun := fun s => ⟨H (1, s), mem_sphere_zero_iff_norm.2 (hH1 _)⟩
      continuous_toFun := (hHc.comp (continuous_const.prodMk continuous_id)).subtype_mk _
      source' := Subtype.ext (hHt0 1)
      target' := Subtype.ext (hHt1 1) }
  refine ⟨n, p, δ, ⟨?_⟩, ?_⟩
  · exact
      { toFun := fun ts => ⟨H ts, mem_sphere_zero_iff_norm.2 (hH1 ts)⟩
        continuous_toFun := hHc.subtype_mk _
        map_zero_left := fun s => Subtype.ext (hH0 s)
        map_one_left := fun s => rfl
        prop' := fun t s hs => by
          rcases hs with rfl | rfl
          · exact Subtype.ext ((hHt0 t).trans (congrArg Subtype.val γ.source.symm))
          · exact Subtype.ext ((hHt1 t).trans (congrArg Subtype.val γ.target.symm)) }
  · intro s
    obtain ⟨i, hi, hs, hs'⟩ := exists_piece hn s.2.1 s.2.2
    refine ⟨i, hi, ?_⟩
    change radialProj (w (1, s)) ∈ _
    rw [hw1]
    exact radialProj_mem_span (polygon_mem_span p hi hs hs')

end InnerProduct

/-! ### A finite union of planes misses a point of the sphere -/

section Avoid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- In dimension at least `3`, the span of two vectors is a proper subspace. -/
theorem span_pair_ne_top (h3 : 3 ≤ finrank ℝ E) (a b : E) : Submodule.span ℝ {a, b} ≠ ⊤ := by
  intro htop
  have h1 : finrank ℝ (Submodule.span ℝ ({a, b} : Set E)) ≤ 2 := by
    classical
    refine (finrank_span_le_card ({a, b} : Set E)).trans ?_
    simp only [Set.toFinset_insert, Set.toFinset_singleton]
    exact Finset.card_le_two
  rw [htop, finrank_top] at h1
  omega

variable [FiniteDimensional ℝ E]

/-- A finite union of planes in a space of dimension at least `3` has empty interior. -/
theorem interior_biUnion_span_pair_eq_empty (h3 : 3 ≤ finrank ℝ E) (p : ℕ → E) (n : ℕ) :
    interior (⋃ i ∈ Finset.range n, (Submodule.span ℝ {p i, p (i + 1)} : Set E)) = ∅ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert,
      interior_union_isClosed_of_interior_empty (Submodule.closed_of_finiteDimensional _) ih]
    by_contra h
    exact span_pair_ne_top h3 (p n) (p (n + 1))
      ((Submodule.span ℝ _).eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.2 h))

/-- A finite union of planes in a space of dimension at least `3` misses some vector. -/
theorem exists_notMem_span_pair (h3 : 3 ≤ finrank ℝ E) (p : ℕ → E) (n : ℕ) :
    ∃ q : E, ∀ i < n, q ∉ Submodule.span ℝ {p i, p (i + 1)} := by
  by_contra hcon
  push Not at hcon
  have huniv : (⋃ i ∈ Finset.range n, (Submodule.span ℝ {p i, p (i + 1)} : Set E)) = univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨i, hi, hq⟩ := hcon q
    exact Set.mem_biUnion (Finset.mem_range.2 hi) hq
  have h := interior_biUnion_span_pair_eq_empty h3 p n
  rw [huniv, interior_univ] at h
  exact (Set.nonempty_iff_ne_empty.1 ⟨0, Set.mem_univ 0⟩) h

/-- A finite union of planes in a space of dimension at least `3` misses some point of the unit
sphere. -/
theorem exists_sphere_notMem_span_pair (h3 : 3 ≤ finrank ℝ E) (p : ℕ → E) (n : ℕ) :
    ∃ q : sphere (0 : E) 1, ∀ i < n, (q : E) ∉ Submodule.span ℝ {p i, p (i + 1)} := by
  obtain ⟨q₀, hq₀⟩ := exists_notMem_span_pair h3 p (n + 1)
  have hne : q₀ ≠ 0 := fun h => hq₀ 0 (Nat.succ_pos n) (h ▸ Submodule.zero_mem _)
  refine ⟨⟨radialProj q₀, radialProj_mem_sphere hne⟩, fun i hi h => ?_⟩
  exact hq₀ i (Nat.lt_succ_of_lt hi) (mem_span_of_radialProj_mem hne h)

end Avoid

/-! ### The sphere minus a point is simply connected -/

/-- The unit sphere of `ℝᵏ⁺¹` minus a point is homeomorphic to `ℝᵏ` (stereographic projection). -/
def sphereComplSingletonHomeomorph {k : ℕ}
    (q : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)) ≃ₜ EuclideanSpace ℝ (Fin k) :=
  haveI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = k + 1) := ⟨finrank_euclideanSpace_fin⟩
  ((Homeomorph.setCongr (stereographic'_source q).symm).trans
    (stereographic' k q).toHomeomorphSourceTarget).trans
    ((Homeomorph.setCongr (stereographic'_target q)).trans (Homeomorph.Set.univ _))

/-- The unit sphere of `ℝᵏ⁺¹` minus a point is contractible. -/
theorem contractibleSpace_sphere_compl_singleton {k : ℕ}
    (q : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    ContractibleSpace ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)) :=
  (sphereComplSingletonHomeomorph q).contractibleSpace

/-- The unit sphere of `ℝᵏ⁺¹` minus a point is simply connected. -/
theorem isSimplyConnected_sphere_compl_singleton {k : ℕ}
    (q : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    IsSimplyConnected ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)) := by
  have := contractibleSpace_sphere_compl_singleton q
  exact SimplyConnectedSpace.ofContractible _

/-! ### Main theorem -/

/-- The unit sphere `Sᵏ ⊆ ℝᵏ⁺¹` is simply connected for `k ≥ 2`. -/
theorem simplyConnectedSpace_sphere_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨?_, fun x γ => ?_⟩
  · rw [← isPathConnected_iff_pathConnectedSpace]
    refine isPathConnected_sphere ?_ 0 zero_le_one
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < k + 1)
  · obtain ⟨n, p, δ, hγδ, hδ⟩ := exists_homotopic_piecewise_geodesic γ
    have h3 : 3 ≤ finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) := by
      rw [finrank_euclideanSpace_fin]
      omega
    obtain ⟨q, hq⟩ := exists_sphere_notMem_span_pair h3 p n
    have hδq : ∀ s, δ s ∈ ({q}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)) := by
      intro s hs
      obtain ⟨i, hi, hmem⟩ := hδ s
      rw [Set.mem_singleton_iff] at hs
      rw [hs] at hmem
      exact hq i hi hmem
    obtain ⟨F, -⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp
      (isSimplyConnected_sphere_compl_singleton q)).2 x δ hδq
    exact hγδ.trans ⟨F⟩

end

end PoincareHighDim

end

/- Source module Submission.Topology.Cellular.CellNeighborhood -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# Cell neighborhoods inside a Euclidean open set

A compact subset of an open Euclidean chart lies in the interior of a closed cell in that
chart. In particular, a proper compact subset of a sphere lies inside a closed cell.
-/

namespace PoincareHighDim

open Set Metric Topology

/-- Enclose a compact subset of an open Euclidean chart in a closed cell. -/
theorem exists_closedCell_in_openEmbedding {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
    {φ : EuclideanSpace ℝ (Fin n) → X} (hφ : IsOpenEmbedding φ)
    {K : Set X} (hK : IsCompact K) (hKφ : K ⊆ range φ) :
    ∃ c : ClosedCell n X, K ⊆ c.interiorSet ∧ c.carrier ⊆ range φ := by
  have hpre : IsCompact (φ ⁻¹' K) := hφ.isInducing.isCompact_preimage' hK hKφ
  obtain ⟨R, hR, hKR⟩ := hpre.isBounded.subset_ball_lt 0 0
  let s : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    Homeomorph.smulOfNeZero R hR.ne'
  let ψ := φ ∘ s
  have hψ : IsOpenEmbedding ψ := hφ.comp s.isOpenEmbedding
  let g : Disk n → X := fun v => ψ v
  have hgi : g '' diskInterior n = ψ '' ball 0 1 := by
    change (ψ ∘ Subtype.val) '' (Subtype.val ⁻¹' ball 0 1) = _
    rw [image_comp, image_preimage_eq_of_subset]
    simpa only [Subtype.range_coe] using (ball_subset_closedBall :
      ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ closedBall 0 1)
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let c : ClosedCell n X :=
    { map := g
      isClosedEmbedding := (hψ.continuous.comp continuous_subtype_val).isClosedEmbedding
        (hψ.injective.comp Subtype.val_injective)
      isOpen_interior := by rw [hgi]; exact hψ.isOpenMap _ isOpen_ball }
  refine ⟨c, ?_, ?_⟩
  · intro x hx
    obtain ⟨v, rfl⟩ := hKφ hx
    have hv : ‖v‖ < R := mem_ball_zero_iff.mp (hKR hx)
    have hnorm : ‖R⁻¹ • v‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
      exact (inv_mul_lt_one₀ hR).mpr hv
    let w : Disk n := ⟨R⁻¹ • v, mem_closedBall_zero_iff.mpr hnorm.le⟩
    refine ⟨w, mem_diskInterior.mpr hnorm, ?_⟩
    change φ (R • (R⁻¹ • v)) = φ v
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  · rintro _ ⟨v, rfl⟩
    exact ⟨s (v : EuclideanSpace ℝ (Fin n)), rfl⟩

/-- Any proper compact subset of the standard sphere has a closed cell neighborhood. -/
theorem exists_closedCell_sphere_of_isCompact {n : ℕ}
    {K : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)}
    (hK : IsCompact K) (hproper : K ≠ univ) :
    ∃ c : ClosedCell n (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      K ⊆ c.interiorSet ∧ c.carrier ≠ univ := by
  obtain ⟨q, hq⟩ := Set.nonempty_compl.mpr hproper
  let e := sphereComplSingletonHomeomorph q
  let φ := Subtype.val ∘ e.symm
  have hφ : IsOpenEmbedding φ :=
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
  have hrange : range φ = {q}ᶜ := by
    change range (Subtype.val ∘ e.symm) = {q}ᶜ
    rw [range_comp, e.symm.surjective.range_eq, image_univ, Subtype.range_coe]
  obtain ⟨c, hKc, hc⟩ := exists_closedCell_in_openEmbedding hφ hK
    (by rw [hrange]; intro x hx heq; exact hq (heq ▸ hx))
  refine ⟨c, hKc, ?_⟩
  intro hu
  have hq' := hc (hu ▸ mem_univ q)
  rw [hrange] at hq'
  exact hq' rfl

end PoincareHighDim

end

/- Source module Submission.Topology.Cellular.RestoreFiber -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# Restoring a collapsed fiber under conjugation

If `f` collapses exactly `K` and a homeomorphism `h` fixes a neighborhood of `f(K)`, then
the conjugate `f⁻¹ ∘ h ∘ f` extends across `K` by the identity. Compactness makes this a
closed embedding. Continuity follows from a closed-graph argument.
-/

namespace PoincareHighDim

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [T2Space Y]

/-- Conjugate through a map with one collapsed fiber and restore that fiber pointwise.

No separate closedness or nonemptiness assumption on `K` is needed. The range formula says
that the image of the restored embedding is the full preimage of the moved range. -/
theorem exists_closedEmbedding_restoreFiber {f : X → Y} {K : Set X}
    (hf : Continuous f) (hfK : CollapsesExactly f K) (h : Y ≃ₜ Y)
    {V : Set Y} (hV : IsOpen V) (hKV : f '' K ⊆ V)
    (hfix : ∀ y ∈ V, h y = y) (hrange : h '' range f ⊆ range f) :
    ∃ g : X → X, IsClosedEmbedding g ∧
      (∀ x, f (g x) = h (f x)) ∧
      (∀ x, f x ∈ V → g x = x) ∧
      (∀ x, g x ∈ K ↔ x ∈ K) ∧
      range g = f ⁻¹' (h '' range f) := by
  classical
  have hlift (x : X) : ∃ y, f y = h (f x) :=
    hrange ⟨f x, mem_range_self x, rfl⟩
  let lift : X → X := fun x => Classical.choose (hlift x)
  have hlift_eq (x : X) : f (lift x) = h (f x) := Classical.choose_spec (hlift x)
  let g : X → X := fun x => if f x ∈ V then x else lift x
  have hgfix (x : X) (hx : f x ∈ V) : g x = x := if_pos hx
  have hgfixK (x : X) (hx : x ∈ K) : g x = x :=
    hgfix x (hKV ⟨x, hx, rfl⟩)
  have hgf (x : X) : f (g x) = h (f x) := by
    by_cases hx : f x ∈ V
    · rw [hgfix x hx, hfix _ hx]
    · exact (congrArg f (if_neg hx)).trans (hlift_eq x)
  have hpreV (y : Y) (hy : h y ∈ V) : y ∈ V := by
    have he : h y = y := h.injective (hfix (h y) hy)
    exact he ▸ hy
  have hgK (x : X) : g x ∈ K ↔ x ∈ K := by
    constructor
    · intro hx
      have hv : h (f x) ∈ V := hgf x ▸ hKV ⟨g x, hx, rfl⟩
      rwa [hgfix x (hpreV _ hv)] at hx
    · intro hx
      rwa [hgfixK x hx]
  have hginj : Function.Injective g := by
    intro x y hxy
    have he : f x = f y := h.injective (by rw [← hgf x, ← hgf y, hxy])
    rcases (hfK x y).mp he with he | ⟨hx, hy⟩
    · exact he
    · rwa [hgfixK x hx, hgfixK y hy] at hxy
  have hgraph : g.graph =
      {p : X × X | f p.2 = h (f p.1)} ∩
        ({p : X × X | f p.1 ∉ V} ∪ {p : X × X | p.2 = p.1}) := by
    ext ⟨x, y⟩
    change g x = y ↔ f y = h (f x) ∧ (f x ∉ V ∨ y = x)
    constructor
    · rintro rfl
      refine ⟨hgf x, ?_⟩
      by_cases hx : f x ∈ V
      · exact Or.inr (hgfix x hx)
      · exact Or.inl hx
    · rintro ⟨hfxy, hxy⟩
      by_cases hx : f x ∈ V
      · exact (hgfix x hx).trans (hxy.resolve_left (not_not.mpr hx)).symm
      · rcases (hfK (g x) y).mp ((hgf x).trans hfxy.symm) with he | ⟨hgx, _⟩
        · exact he
        · exact (hx (hKV ⟨x, (hgK x).mp hgx, rfl⟩)).elim
  have hgcont : Continuous g := by
    apply continuous_from_closed_graph
    rw [hgraph]
    exact (isClosed_eq (hf.comp continuous_snd)
      (h.continuous.comp (hf.comp continuous_fst))).inter
        ((hV.preimage (hf.comp continuous_fst)).isClosed_compl.union
          (isClosed_eq continuous_snd continuous_fst))
  refine ⟨g, hgcont.isClosedEmbedding hginj, hgf, hgfix, hgK, ?_⟩
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f x, mem_range_self x, (hgf x).symm⟩
  · rintro ⟨y, ⟨x, rfl⟩, he⟩
    by_cases hz : z ∈ K
    · exact ⟨z, hgfixK z hz⟩
    · refine ⟨x, ?_⟩
      exact ((hfK (g x) z).mp ((hgf x).trans he)).resolve_right (fun hk => hz hk.2)

omit [TopologicalSpace X] [CompactSpace X] [T2Space X] [T2Space Y] in
/-- A restored embedding carries every saturated subset to the corresponding moved subset.
In particular, this applies to preimages of open neighborhoods of the collapsed value. -/
theorem image_preimage_of_restored_range {f : X → Y} {g : X → X} (h : Y ≃ₜ Y)
    (hgf : ∀ x, f (g x) = h (f x)) (hrange : range g = f ⁻¹' (h '' range f))
    (S : Set Y) : g '' (f ⁻¹' S) = f ⁻¹' (h '' (S ∩ range f)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨hx, mem_range_self x⟩, (hgf x).symm⟩
  · rintro ⟨y, ⟨hyS, hyf⟩, hyz⟩
    have hzg : z ∈ range g := by
      rw [hrange]
      exact ⟨y, hyf, hyz⟩
    obtain ⟨x, rfl⟩ := hzg
    refine ⟨x, ?_, rfl⟩
    have he : y = f x := h.injective (hyz.trans (hgf x))
    show f x ∈ S
    exact he ▸ hyS

omit [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X] [T2Space Y] in
/-- A subset containing the collapsed fiber is saturated. -/
theorem CollapsesExactly.preimage_image_eq_of_subset {f : X → Y} {K S : Set X}
    (hfK : CollapsesExactly f K) (hKS : K ⊆ S) : f ⁻¹' (f '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (hfK y x).mp hxy with rfl | ⟨_, hx⟩
    · exact hy
    · exact hKS hx
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [TopologicalSpace X] [CompactSpace X] [T2Space X] [T2Space Y] in
/-- The image formula for any subset containing the collapsed fiber. -/
theorem image_of_restored_range {f : X → Y} {g : X → X} {K S : Set X}
    (hfK : CollapsesExactly f K) (hKS : K ⊆ S) (h : Y ≃ₜ Y)
    (hgf : ∀ x, f (g x) = h (f x)) (hrange : range g = f ⁻¹' (h '' range f)) :
    g '' S = f ⁻¹' (h '' (f '' S)) := by
  have hh := image_preimage_of_restored_range h hgf hrange (f '' S)
  rw [hfK.preimage_image_eq_of_subset hKS,
    inter_eq_left.mpr (image_subset_range f S)] at hh
  exact hh

omit [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X] [T2Space Y] in
/-- A subset containing both exceptional fibers is saturated. -/
theorem preimage_image_eq_of_two_fibers {f : X → Y} {A B S : Set X}
    (hfAB : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (hAS : A ⊆ S) (hBS : B ⊆ S) : f ⁻¹' (f '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (hfAB y x).mp hxy with rfl | ⟨_, hx⟩ | ⟨_, hx⟩
    · exact hy
    · exact hAS hx
    · exact hBS hx
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [TopologicalSpace X] [CompactSpace X] [T2Space X] [T2Space Y] in
/-- The restored image formula for subsets containing both exceptional fibers. -/
theorem image_of_restored_range_two {f : X → Y} {g : X → X} {A B S : Set X}
    (hfAB : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (hAS : A ⊆ S) (hBS : B ⊆ S) (h : Y ≃ₜ Y)
    (hgf : ∀ x, f (g x) = h (f x)) (hrange : range g = f ⁻¹' (h '' range f)) :
    g '' S = f ⁻¹' (h '' (f '' S)) := by
  have hh := image_preimage_of_restored_range h hgf hrange (f '' S)
  rw [preimage_image_eq_of_two_fibers hfAB hAS hBS,
    inter_eq_left.mpr (image_subset_range f S)] at hh
  exact hh

omit [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X] [T2Space Y] in
/-- Postcomposing with an injective function preserves the collapsed fiber. -/
theorem CollapsesExactly.comp_injective {Z : Type*} {f : X → Y} {c : Y → Z} {K : Set X}
    (hfK : CollapsesExactly f K) (hc : Function.Injective c) :
    CollapsesExactly (c ∘ f) K :=
  fun x y => hc.eq_iff.trans (hfK x y)

/-- Restore the first of two collapsed fibers while moving the entire range away from the
second. The resulting continuous map collapses precisely the second fiber.

The moved range must avoid `f(B)`. Together with `h = id` on `V`, this already forces
`V` to avoid `f(B)`, so that condition need not be supplied separately. -/
theorem exists_continuous_restoreFirstFiber {f : X → Y} {A B : Set X}
    (hf : Continuous f)
    (hfAB : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (hAB : Disjoint A B) (h : Y ≃ₜ Y)
    {V : Set Y} (hV : IsOpen V) (hAV : f '' A ⊆ V)
    (hfix : ∀ y ∈ V, h y = y) (hrange : h '' range f ⊆ range f)
    (havoid : Disjoint (h '' range f) (f '' B)) :
    ∃ g : X → X, Continuous g ∧ CollapsesExactly g B ∧
      (∀ x, f (g x) = h (f x)) ∧
      (∀ x, f x ∈ V → g x = x) ∧
      (∀ x, g x ∈ A ↔ x ∈ A) ∧
      (∀ x, g x ∉ B) ∧
      range g = f ⁻¹' (h '' range f) := by
  classical
  have hlift (x : X) : ∃ y, f y = h (f x) :=
    hrange ⟨f x, mem_range_self x, rfl⟩
  let lift : X → X := fun x => Classical.choose (hlift x)
  have hlift_eq (x : X) : f (lift x) = h (f x) := Classical.choose_spec (hlift x)
  let g : X → X := fun x => if f x ∈ V then x else lift x
  have hgfix (x : X) (hx : f x ∈ V) : g x = x := if_pos hx
  have hgfixA (x : X) (hx : x ∈ A) : g x = x :=
    hgfix x (hAV ⟨x, hx, rfl⟩)
  have hgf (x : X) : f (g x) = h (f x) := by
    by_cases hx : f x ∈ V
    · rw [hgfix x hx, hfix _ hx]
    · exact (congrArg f (if_neg hx)).trans (hlift_eq x)
  have hpreV (y : Y) (hy : h y ∈ V) : y ∈ V := by
    have he : h y = y := h.injective (hfix (h y) hy)
    exact he ▸ hy
  have hgA (x : X) : g x ∈ A ↔ x ∈ A := by
    constructor
    · intro hx
      have hv : h (f x) ∈ V := hgf x ▸ hAV ⟨g x, hx, rfl⟩
      rwa [hgfix x (hpreV _ hv)] at hx
    · intro hx
      rwa [hgfixA x hx]
  have hgnotB (x : X) : g x ∉ B := by
    intro hx
    exact Set.disjoint_left.mp havoid ⟨f x, mem_range_self x, (hgf x).symm⟩
      ⟨g x, hx, rfl⟩
  have hgB : CollapsesExactly g B := by
    intro x y
    constructor
    · intro hxy
      have he : f x = f y := h.injective (by rw [← hgf x, ← hgf y, hxy])
      rcases (hfAB x y).mp he with he | ⟨hx, hy⟩ | hxyB
      · exact Or.inl he
      · exact Or.inl (by rwa [hgfixA x hx, hgfixA y hy] at hxy)
      · exact Or.inr hxyB
    · rintro (rfl | ⟨hx, hy⟩)
      · rfl
      · have hxy : f x = f y := (hfAB x y).mpr (Or.inr (Or.inr ⟨hx, hy⟩))
        have he : f (g x) = f (g y) := by rw [hgf, hgf, hxy]
        rcases (hfAB (g x) (g y)).mp he with he | ⟨hgx, _⟩ | ⟨hgx, _⟩
        · exact he
        · exact (Set.disjoint_left.mp hAB ((hgA x).mp hgx) hx).elim
        · exact (hgnotB x hgx).elim
  have hgraph : g.graph =
      {p : X × X | f p.2 = h (f p.1)} ∩
        ({p : X × X | f p.1 ∉ V} ∪ {p : X × X | p.2 = p.1}) := by
    ext ⟨x, y⟩
    change g x = y ↔ f y = h (f x) ∧ (f x ∉ V ∨ y = x)
    constructor
    · rintro rfl
      refine ⟨hgf x, ?_⟩
      by_cases hx : f x ∈ V
      · exact Or.inr (hgfix x hx)
      · exact Or.inl hx
    · rintro ⟨hfxy, hxy⟩
      by_cases hx : f x ∈ V
      · exact (hgfix x hx).trans (hxy.resolve_left (not_not.mpr hx)).symm
      · rcases (hfAB (g x) y).mp ((hgf x).trans hfxy.symm) with he | ⟨hgx, _⟩ | ⟨hgx, _⟩
        · exact he
        · exact (hx (hAV ⟨x, (hgA x).mp hgx, rfl⟩)).elim
        · exact (hgnotB x hgx).elim
  have hgcont : Continuous g := by
    apply continuous_from_closed_graph
    rw [hgraph]
    exact (isClosed_eq (hf.comp continuous_snd)
      (h.continuous.comp (hf.comp continuous_fst))).inter
        ((hV.preimage (hf.comp continuous_fst)).isClosed_compl.union
          (isClosed_eq continuous_snd continuous_fst))
  refine ⟨g, hgcont, hgB, hgf, hgfix, hgA, hgnotB, ?_⟩
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f x, mem_range_self x, (hgf x).symm⟩
  · rintro ⟨y, ⟨x, rfl⟩, he⟩
    by_cases hz : z ∈ A
    · exact ⟨z, hgfixA z hz⟩
    · refine ⟨x, ?_⟩
      rcases (hfAB (g x) z).mp ((hgf x).trans he) with he | ⟨_, hzA⟩ | ⟨hgx, _⟩
      · exact he
      · exact (hz hzA).elim
      · exact (hgnotB x hgx).elim

end PoincareHighDim

end

/- Source module Submission.Topology.Schoenflies.SaturatedImage -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# Open images of saturated subsets

A continuous map from a compact space is a closed map. A saturated open set therefore has
open image wherever that image lies in the ambient interior of the range. This is the
openness fact needed in the cellular argument, without an appeal to invariance of domain.
-/

namespace PoincareHighDim

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] {f : X → Y}

/-- A saturated open set whose image lies in an open subset of the range has open image
in the ambient target. -/
theorem isOpen_image_of_saturated (hf : Continuous f) {U : Set X} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : f '' U ⊆ V) (hVrange : V ⊆ range f)
    (hsat : ∀ x y, f x = f y → x ∈ U → y ∈ U) : IsOpen (f '' U) := by
  have heq : f '' U = V \ f '' Uᶜ := by
    ext y
    constructor
    · rintro hy
      refine ⟨hUV hy, ?_⟩
      obtain ⟨x, hx, rfl⟩ := hy
      rintro ⟨z, hz, hzx⟩
      exact hz (hsat x z hzx.symm hx)
    · rintro ⟨hy, hnot⟩
      obtain ⟨x, rfl⟩ := hVrange hy
      refine ⟨x, ?_, rfl⟩
      by_contra hx
      exact hnot ⟨x, hx, rfl⟩
  rw [heq]
  exact hV.sdiff ((hU.isClosed_compl.isCompact.image hf).isClosed)

/-- It suffices for the image to lie in the interior of the range. -/
theorem isOpen_image_of_saturated_of_subset_interior (hf : Continuous f) {U : Set X}
    (hU : IsOpen U) (hUV : f '' U ⊆ interior (range f))
    (hsat : ∀ x y, f x = f y → x ∈ U → y ∈ U) : IsOpen (f '' U) :=
  isOpen_image_of_saturated hf hU isOpen_interior hUV interior_subset hsat

end PoincareHighDim

end

/- Source module Submission.Topology.Cellular.RadialCompression -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# Radial compression fixing a neighborhood of the origin

A radial stretch fixes the closed ball of radius `δ` and replaces every larger radius `r`
by `δ + c * (r - δ)`, where `c > 0`. Its inverse uses the reciprocal stretch factor.
This gives ambient homeomorphisms compressing a prescribed ball into a smaller ball while
fixing a neighborhood of the origin.
-/

namespace PoincareHighDim

open Metric Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A radial stretch with an unchanged central ball. -/
def radialStretch (δ c : ℝ) (x : E) : E :=
  ((δ + c * (max δ ‖x‖ - δ)) / max δ ‖x‖) • x

theorem radialStretch_of_norm_le {δ c : ℝ} (hδ : 0 < δ) {x : E}
    (hx : ‖x‖ ≤ δ) : radialStretch δ c x = x := by
  simp [radialStretch, max_eq_left hx, hδ.ne']

theorem radialStretch_of_le_norm {δ c : ℝ} {x : E} (hx : δ ≤ ‖x‖) :
    radialStretch δ c x = ((δ + c * (‖x‖ - δ)) / ‖x‖) • x := by
  rw [radialStretch, max_eq_right hx]

theorem continuous_radialStretch {δ c : ℝ} (hδ : 0 < δ) :
    Continuous (radialStretch δ c : E → E) := by
  apply Continuous.smul
  · exact (continuous_const.add (continuous_const.mul
      ((continuous_const.max continuous_norm).sub continuous_const))).div
      (continuous_const.max continuous_norm)
      (fun x => ne_of_gt (lt_of_lt_of_le hδ (le_max_left δ ‖x‖)))
  · exact continuous_id

theorem norm_radialStretch_of_le_norm {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    {x : E} (hx : δ ≤ ‖x‖) :
    ‖radialStretch δ c x‖ = δ + c * (‖x‖ - δ) := by
  have hn : 0 < ‖x‖ := hδ.trans_le hx
  have hp : 0 < δ + c * (‖x‖ - δ) := by positivity
  rw [radialStretch_of_le_norm hx, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact div_mul_cancel₀ _ hn.ne'

theorem radialStretch_inverse {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (x : E) :
    radialStretch δ c⁻¹ (radialStretch δ c x) = x := by
  by_cases hx : ‖x‖ ≤ δ
  · rw [radialStretch_of_norm_le hδ hx, radialStretch_of_norm_le hδ hx]
  · have hx' : δ < ‖x‖ := lt_of_not_ge hx
    have hn : 0 < ‖x‖ := hδ.trans hx'
    have hp : 0 < δ + c * (‖x‖ - δ) := by positivity
    have hy : δ ≤ ‖radialStretch δ c x‖ := by
      rw [norm_radialStretch_of_le_norm hδ hc hx'.le]
      exact le_add_of_nonneg_right (mul_nonneg hc.le (sub_nonneg.mpr hx'.le))
    rw [radialStretch_of_le_norm hy, norm_radialStretch_of_le_norm hδ hc hx'.le,
      radialStretch_of_le_norm hx'.le, smul_smul]
    have heq : (δ + c⁻¹ * (δ + c * (‖x‖ - δ) - δ)) /
        (δ + c * (‖x‖ - δ)) * ((δ + c * (‖x‖ - δ)) / ‖x‖) = 1 := by
      field_simp
      ring
    rw [heq, one_smul]

/-- The radial homeomorphism fixing radius `δ` and multiplying radial distances beyond it
by the positive factor `c`. -/
def radialStretchHomeomorph (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c) : E ≃ₜ E where
  toFun := radialStretch δ c
  invFun := radialStretch δ c⁻¹
  left_inv := radialStretch_inverse hδ hc
  right_inv x := by
    simpa using radialStretch_inverse hδ (inv_pos.mpr hc) x
  continuous_toFun := continuous_radialStretch hδ
  continuous_invFun := continuous_radialStretch hδ

/-- Compress a prescribed closed ball into a smaller open ball while fixing a still smaller
closed ball pointwise. -/
theorem exists_radial_compression {δ ε R : ℝ} (hδ : 0 < δ) (hδε : δ < ε) (hεR : ε < R) :
    ∃ h : E ≃ₜ E,
      (∀ x, ‖x‖ ≤ δ → h x = x) ∧
      MapsTo h (closedBall 0 R) (ball 0 ε) := by
  let c : ℝ := ((δ + ε) / 2 - δ) / (R - δ)
  have hδR : δ < R := hδε.trans hεR
  have hc : 0 < c := div_pos (by linarith) (sub_pos.mpr hδR)
  refine ⟨radialStretchHomeomorph δ c hδ hc, ?_, ?_⟩
  · intro x hx
    exact radialStretch_of_norm_le hδ hx
  · intro x hx
    rw [mem_ball_zero_iff]
    change ‖radialStretch δ c x‖ < ε
    by_cases hxδ : ‖x‖ ≤ δ
    · rw [radialStretch_of_norm_le hδ hxδ]
      exact hxδ.trans_lt hδε
    · rw [norm_radialStretch_of_le_norm hδ hc (le_of_not_ge hxδ)]
      have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
      have hmul : c * (‖x‖ - δ) ≤ c * (R - δ) := mul_le_mul_of_nonneg_left
        (sub_le_sub_right hxR δ) hc.le
      have hcancel : c * (R - δ) = (δ + ε) / 2 - δ := by
        dsimp [c]
        exact div_mul_cancel₀ _ (sub_ne_zero.mpr hδR.ne')
      rw [hcancel] at hmul
      linarith

/-- Radial compression can be confined to any larger ball. -/
theorem exists_radial_compression_supported {δ ε R S : ℝ}
    (hδ : 0 < δ) (hδε : δ < ε) (hεR : ε < R) (hRS : R < S) :
    ∃ h : E ≃ₜ E,
      (∀ x, ‖x‖ ≤ δ → h x = x) ∧
      MapsTo h (closedBall 0 R) (ball 0 ε) ∧
      (∀ x, S ≤ ‖x‖ → h x = x) := by
  let η : ℝ := (δ + ε) / 2
  have hδη : δ < η := by dsimp [η]; linarith
  have hηε : η < ε := by dsimp [η]; linarith
  have hδR : δ < R := hδε.trans hεR
  have hηS : η < S := hηε.trans (hεR.trans hRS)
  have hη : 0 < η := hδ.trans hδη
  have hS : 0 < S := hη.trans hηS
  let c : ℝ := (η - δ) / (R - δ)
  let d : ℝ := (S - η) / (S - R)
  have hc : 0 < c := div_pos (sub_pos.mpr hδη) (sub_pos.mpr hδR)
  have hd : 0 < d := div_pos (sub_pos.mpr hηS) (sub_pos.mpr hRS)
  have hcR : c * (R - δ) = η - δ := div_mul_cancel₀ _ (sub_ne_zero.mpr hδR.ne')
  have hdS : d * (S - R) = S - η := div_mul_cancel₀ _ (sub_ne_zero.mpr hRS.ne')
  let h₁ : E ≃ₜ E := radialStretchHomeomorph δ c hδ hc
  let h₂ : E ≃ₜ E := radialStretchHomeomorph η (d / c) hη (div_pos hd hc)
  let h₃ : E ≃ₜ E := radialStretchHomeomorph S d⁻¹ hS (inv_pos.mpr hd)
  refine ⟨(h₁.trans h₂).trans h₃, ?_, ?_, ?_⟩
  · intro x hx
    change radialStretch S d⁻¹ (radialStretch η (d / c) (radialStretch δ c x)) = x
    rw [radialStretch_of_norm_le hδ hx,
      radialStretch_of_norm_le hη (hx.trans hδη.le),
      radialStretch_of_norm_le hS ((hx.trans hδη.le).trans hηS.le)]
  · intro x hx
    have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
    have hx₁ : ‖radialStretch δ c x‖ ≤ η := by
      by_cases hxδ : ‖x‖ ≤ δ
      · rw [radialStretch_of_norm_le hδ hxδ]
        exact hxδ.trans hδη.le
      · rw [norm_radialStretch_of_le_norm hδ hc (le_of_not_ge hxδ)]
        have := mul_le_mul_of_nonneg_left (sub_le_sub_right hxR δ) hc.le
        linarith [hcR]
    rw [mem_ball_zero_iff]
    change ‖radialStretch S d⁻¹ (radialStretch η (d / c) (radialStretch δ c x))‖ < ε
    rw [radialStretch_of_norm_le hη hx₁,
      radialStretch_of_norm_le hS (hx₁.trans hηS.le)]
    exact hx₁.trans_lt hηε
  · intro x hx
    have hxδ : δ ≤ ‖x‖ := hδR.le.trans (hRS.le.trans hx)
    have hx₁η : η ≤ ‖radialStretch δ c x‖ := by
      rw [norm_radialStretch_of_le_norm hδ hc hxδ]
      have := mul_le_mul_of_nonneg_left (sub_le_sub_right (hRS.le.trans hx) δ) hc.le
      linarith [hcR]
    have heq : η + (d / c) * (δ + c * (‖x‖ - δ) - η) = η + d * (‖x‖ - R) := by
      have hηeq : η = δ + c * (R - δ) := by linarith [hcR]
      rw [hηeq]
      field_simp
      ring
    have hx₂ : ‖radialStretch η (d / c) (radialStretch δ c x)‖ =
        η + d * (‖x‖ - R) := by
      rw [norm_radialStretch_of_le_norm hη (div_pos hd hc) hx₁η,
        norm_radialStretch_of_le_norm hδ hc hxδ, heq]
    have hx₂S : S ≤ ‖radialStretch η (d / c) (radialStretch δ c x)‖ := by
      rw [hx₂]
      have := mul_le_mul_of_nonneg_left (sub_le_sub_right hx R) hd.le
      linarith [hdS]
    have hn : 0 < ‖x‖ := hS.trans_le hx
    have hu : 0 < δ + c * (‖x‖ - δ) := by positivity
    have hv : 0 < η + d * (‖x‖ - R) := by
      have : 0 ≤ ‖x‖ - R := sub_nonneg.mpr (hRS.le.trans hx)
      positivity
    have hw : S + d⁻¹ * (η + d * (‖x‖ - R) - S) = ‖x‖ := by
      have hSeq : S = η + d * (S - R) := by linarith [hdS]
      calc
        _ = S + d⁻¹ * (d * (‖x‖ - S)) := by congr 2; nlinarith [hdS]
        _ = ‖x‖ := by field_simp; ring
    change radialStretch S d⁻¹ (radialStretch η (d / c) (radialStretch δ c x)) = x
    rw [radialStretch_of_le_norm hx₂S, hx₂, hw,
      radialStretch_of_le_norm hx₁η, norm_radialStretch_of_le_norm hδ hc hxδ,
      heq, radialStretch_of_le_norm hxδ, smul_smul, smul_smul]
    have hscalar : (‖x‖ / (η + d * (‖x‖ - R))) *
        ((η + d * (‖x‖ - R)) / (δ + c * (‖x‖ - δ))) *
        ((δ + c * (‖x‖ - δ)) / ‖x‖) = 1 := by
      field_simp
    rw [hscalar, one_smul]

end

end PoincareHighDim

end

/- Source module Submission.Topology.Schoenflies.SphereCompression -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# Compressing a proper compact subset of a sphere

Delete a point outside the compact set and use stereographic coordinates centered at the
chosen point. Radial compression in these coordinates fixes a neighborhood of the chosen
point. Extending the coordinate homeomorphism to the one-point compactification produces
the required homeomorphism of the whole sphere.
-/

namespace PoincareHighDim

open Set Metric Topology Filter

noncomputable section

/-- In a compact Hausdorff space with a Euclidean puncture, a compact set avoiding the puncture
can be compressed into any neighborhood of a chosen point, fixing a smaller neighborhood. -/
theorem exists_compression_of_compl_singleton_homeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (q : X) (e : ({q}ᶜ : Set X) ≃ₜ E) {K U : Set X}
    (hK : IsCompact K) (hqK : q ∉ K) {a : X} (haq : a ≠ q)
    (hU : IsOpen U) (haU : a ∈ U) :
    ∃ h : X ≃ₜ X, h '' K ⊆ U ∧
      ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ ∀ x ∈ V, h x = x := by
  let a' : ({q}ᶜ : Set X) := ⟨a, haq⟩
  let c : E ≃ₜ ({q}ᶜ : Set X) := (Homeomorph.addRight (e a')).trans e.symm
  let φ : E → X := fun x => (c x).1
  have hφ : IsOpenEmbedding φ :=
    (isOpen_compl_singleton.isOpenEmbedding_subtypeVal).comp c.isOpenEmbedding
  have hφrange : range φ = {q}ᶜ := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (c v).2
    · intro hx
      refine ⟨c.symm ⟨x, hx⟩, ?_⟩
      exact congrArg Subtype.val (c.apply_symm_apply ⟨x, hx⟩)
  have hφ0 : φ 0 = a := by
    change (e.symm (0 + e a')).1 = a
    rw [zero_add, e.symm_apply_apply]
  have hKφ : K ⊆ range φ := by
    rw [hφrange]
    intro x hx hxeq
    exact hqK (hxeq ▸ hx)
  have hKE : IsCompact (φ ⁻¹' K) := hφ.isInducing.isCompact_preimage' hK hKφ
  have hU0 : φ ⁻¹' U ∈ 𝓝 (0 : E) :=
    (hU.preimage hφ.continuous).mem_nhds (by simpa only [mem_preimage, hφ0] using haU)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU0
  obtain ⟨R, hεR, hKR⟩ := hKE.isBounded.subset_closedBall_lt ε (0 : E)
  obtain ⟨r, hrfix, hrK⟩ := exists_radial_compression
    (E := E) (δ := ε / 2) (by positivity) (by linarith) hεR
  let j : OnePoint E ≃ₜ X :=
    OnePoint.equivOfIsEmbeddingOfRangeEq q φ hφ.isEmbedding hφrange
  have hj (x : E) : j (x : OnePoint E) = φ x := rfl
  let h : X ≃ₜ X := (j.symm.trans r.onePointCongr).trans j
  have hh (x : E) : h (φ x) = φ (r x) := by
    change j (r.onePointCongr (j.symm (φ x))) = φ (r x)
    rw [← hj x, j.symm_apply_apply]
    exact hj (r x)
  refine ⟨h, ?_, φ '' ball 0 (ε / 2), hφ.isOpenMap _ isOpen_ball, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨v, rfl⟩ := hKφ hx
    rw [hh]
    exact hεU (hrK (hKR hx))
  · exact ⟨0, mem_ball_self (by positivity), hφ0⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [hh, hrfix x (mem_ball_zero_iff.mp hx).le]

/-- A proper compact subset of a sphere can be compressed into any neighborhood of one of
its points, by a homeomorphism fixing a smaller neighborhood of that point. -/
theorem exists_sphere_compression {n : ℕ}
    {K U : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)}
    (hK : IsCompact K) (hproper : K ≠ univ)
    {a : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1} (ha : a ∈ K)
    (hU : IsOpen U) (haU : a ∈ U) :
    ∃ h : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₜ
        sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      h '' K ⊆ U ∧ ∃ V, IsOpen V ∧ a ∈ V ∧ ∀ x ∈ V, h x = x := by
  obtain ⟨q, hq⟩ := Set.nonempty_compl.mpr hproper
  exact exists_compression_of_compl_singleton_homeomorph q (sphereComplSingletonHomeomorph q)
    hK hq (fun heq => hq (heq ▸ ha)) hU haU

end

end PoincareHighDim

end

/- Source module Submission.Topology.Cellular.CellularFiber -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# Cell neighborhoods of a collapsed fiber

Conjugating a compression through a map with one collapsed fiber, and restoring that fiber
pointwise, produces smaller embedded cells. The openness hypothesis on the image of the
open disk replaces any use of invariance of domain.
-/

namespace PoincareHighDim

open Set Metric Topology

section Restore

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : Disk n → Y} {K U : Set (Disk n)}

/-- Restoring a fiber after compressing the image yields a closed-cell neighborhood of it. -/
theorem exists_closedCell_of_restored_compression (hf : Continuous f)
    (hfK : CollapsesExactly f K) (hKI : K ⊆ diskInterior n)
    (hfI : IsOpen (f '' diskInterior n)) (hKU : K ⊆ U)
    (h : Y ≃ₜ Y) (hmove : h '' range f ⊆ f '' U)
    {V : Set Y} (hV : IsOpen V) (hKV : f '' K ⊆ V)
    (hfix : ∀ y ∈ V, h y = y) :
    ∃ c : ClosedCell n (Disk n), K ⊆ c.interiorSet ∧ c.carrier ⊆ U := by
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  obtain ⟨g, hg, hgf, hgfix, -, hgrange⟩ := exists_closedEmbedding_restoreFiber hf hfK h
    hV hKV hfix (hmove.trans (image_subset_range f U))
  have hI : g '' diskInterior n = f ⁻¹' (h '' (f '' diskInterior n)) :=
    image_of_restored_range hfK hKI h hgf hgrange
  let c : ClosedCell n (Disk n) := {
    map := g
    isClosedEmbedding := hg
    isOpen_interior := by rw [hI]; exact (h.isOpenMap _ hfI).preimage hf }
  refine ⟨c, ?_, ?_⟩
  · intro x hx
    exact ⟨x, hKI hx, hgfix x (hKV ⟨x, hx, rfl⟩)⟩
  · intro x hx
    have hx' : f x ∈ h '' range f := by
      change x ∈ range g at hx
      rwa [hgrange] at hx
    have : x ∈ f ⁻¹' (f '' U) := hmove hx'
    rwa [hfK.preimage_image_eq_of_subset hKU] at this

end Restore

namespace ClosedCell

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

/-- An open subset of the disk lying in its open interior has open image in the ambient
space under a closed-cell parametrization. -/
theorem isOpen_image_of_subset_interior (c : ClosedCell n X) {U : Set (Disk n)}
    (hU : IsOpen U) (hUI : U ⊆ diskInterior n) : IsOpen (c.map '' U) := by
  obtain ⟨V, hV, heq⟩ := c.isClosedEmbedding.isEmbedding.isInducing.image_eq_isOpen_inter_range hU
  have hsub : c.map '' U ⊆ c.interiorSet := image_mono hUI
  have himage : c.map '' U = V ∩ c.interiorSet := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨(heq ▸ hx).1, hsub hx⟩
    · intro x hx
      rw [heq]
      exact ⟨hx.1, c.interiorSet_subset_carrier hx.2⟩
  rw [himage]
  exact hV.inter c.isOpen_interior

/-- A cell contained in the open disk can be inserted into any ambient cell. -/
def nest (c : ClosedCell n X) (d : ClosedCell n (Disk n))
    (hd : d.carrier ⊆ diskInterior n) : ClosedCell n X where
  map := c.map ∘ d.map
  isClosedEmbedding := c.isClosedEmbedding.comp d.isClosedEmbedding
  isOpen_interior := by
    rw [image_comp]
    exact c.isOpen_image_of_subset_interior d.isOpen_interior
      (d.interiorSet_subset_carrier.trans hd)

@[simp]
theorem nest_carrier (c : ClosedCell n X) (d : ClosedCell n (Disk n))
    (hd : d.carrier ⊆ diskInterior n) : (c.nest d hd).carrier = c.map '' d.carrier :=
  range_comp c.map d.map

@[simp]
theorem nest_interiorSet (c : ClosedCell n X) (d : ClosedCell n (Disk n))
    (hd : d.carrier ⊆ diskInterior n) : (c.nest d hd).interiorSet = c.map '' d.interiorSet :=
  image_comp c.map d.map (diskInterior n)

end ClosedCell

section Sphere

variable {n : ℕ} {f : Disk n → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}
    {K : Set (Disk n)}

/-- A proper sphere-valued map of a disk with one collapsed fiber gives arbitrarily small
cell neighborhoods of that fiber. Each new cell lies in the original open disk. -/
theorem exists_cell_neighborhood_of_collapsesExactly_sphere
    (hf : Continuous f) (hfK : CollapsesExactly f K) (hKne : K.Nonempty)
    (hKI : K ⊆ diskInterior n) (hproper : range f ≠ univ)
    (hfI : IsOpen (f '' diskInterior n))
    (U : Set (Disk n)) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ c : ClosedCell n (Disk n), K ⊆ c.interiorSet ∧
      c.carrier ⊆ U ∩ diskInterior n := by
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let W := U ∩ diskInterior n
  have hKW : K ⊆ W := subset_inter hKU hKI
  have hW : IsOpen W := hU.inter (isOpen_diskInterior n)
  have hfW : IsOpen (f '' W) := isOpen_image_of_saturated hf hW hfI
    (image_mono inter_subset_right) (image_subset_range _ _) (by
      intro x y hxy hx
      rcases (hfK x y).mp hxy with rfl | ⟨-, hy⟩
      · exact hx
      · exact hKW hy)
  obtain ⟨x, hx⟩ := hKne
  obtain ⟨h, hmove, V, hV, haV, hfix⟩ := exists_sphere_compression
    (isCompact_range hf) hproper (mem_range_self x) hfW ⟨x, hKW hx, rfl⟩
  have hKV : f '' K ⊆ V := by
    rintro y ⟨z, hz, rfl⟩
    have heq : f z = f x := (hfK z x).mpr (Or.inr ⟨hz, hx⟩)
    rwa [heq]
  exact exists_closedCell_of_restored_compression hf hfK hKI hfI hKW h hmove hV hKV hfix

/-- **One-fiber cellularity.** A compact exceptional fiber in the interior of a disk is
cellular if collapsing it embeds the quotient in the sphere with open interior image. -/
theorem isCellular_of_collapsesExactly_sphere
    (hf : Continuous f) (hfK : CollapsesExactly f K) (hK : IsCompact K)
    (hKne : K.Nonempty) (hKI : K ⊆ diskInterior n) (hproper : range f ≠ univ)
    (hfI : IsOpen (f '' diskInterior n)) : IsCellular n K := by
  apply isCellular_of_cell_neighborhoods hK.isClosed hKne
  intro U hU hKU
  obtain ⟨c, hKc, hcU⟩ := exists_cell_neighborhood_of_collapsesExactly_sphere
    hf hfK hKne hKI hproper hfI U hU hKU
  exact ⟨c, hKc, hcU.trans inter_subset_left⟩

/-- The one-fiber criterion also proves cellularity in an ambient space containing the
original disk as a closed cell. -/
theorem ClosedCell.isCellular_image_of_collapsesExactly_sphere
    {X : Type*} [MetricSpace X] (c : ClosedCell n X)
    (hf : Continuous f) (hfK : CollapsesExactly f K) (hK : IsCompact K)
    (hKne : K.Nonempty) (hKI : K ⊆ diskInterior n) (hproper : range f ≠ univ)
    (hfI : IsOpen (f '' diskInterior n)) : IsCellular n (c.map '' K) := by
  apply isCellular_of_cell_neighborhoods
    (hK.image c.isClosedEmbedding.continuous).isClosed (hKne.image c.map)
  intro U hU hKU
  have hKpre : K ⊆ c.map ⁻¹' U := fun x hx => hKU ⟨x, hx, rfl⟩
  obtain ⟨d, hKd, hd⟩ := exists_cell_neighborhood_of_collapsesExactly_sphere
    hf hfK hKne hKI hproper hfI (c.map ⁻¹' U)
    (hU.preimage c.isClosedEmbedding.continuous) hKpre
  refine ⟨c.nest d (hd.trans inter_subset_right), ?_, ?_⟩
  · rw [ClosedCell.nest_interiorSet]
    exact image_mono hKd
  · rw [ClosedCell.nest_carrier]
    rintro x ⟨y, hy, rfl⟩
    exact (hd hy).1

end Sphere

end PoincareHighDim

end

/- Source module Submission.Topology.Disks.HomeomorphExtension -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# Extending a homeomorphism by the identity

A homeomorphism of a closed subset fixing its frontier extends to the ambient space by the
identity. In particular, a boundary-fixing homeomorphism of an embedded closed disk extends
whenever the image of the open disk is open.
-/

namespace PoincareHighDim

open Set Topology Metric

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem continuous_subtypeCongr_identity {C : Set X} (hC : IsClosed C)
    (e : C ≃ₜ C) (hfix : ∀ x : C, (x : X) ∈ frontier C → e x = x) :
    Continuous (by
      classical
      exact fun x : X => e.toEquiv.subtypeCongr (Equiv.refl {x // x ∉ C}) x) := by
  classical
  let f : X → X := e.toEquiv.subtypeCongr (Equiv.refl {x // x ∉ C})
  have hfC : ContinuousOn f C := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : C => f x)
    have h : (fun x : C => f x) = fun x : C => (e x : X) := by
      funext x
      exact Equiv.Perm.subtypeCongr.left_apply_subtype _ _ x
    rw [h]
    exact continuous_subtype_val.comp e.continuous
  have hfid : ∀ x ∈ closure Cᶜ, f x = x := by
    intro x hx
    by_cases hxC : x ∈ C
    · exact (Equiv.Perm.subtypeCongr.left_apply e.toEquiv
        (Equiv.refl {x // x ∉ C}) hxC).trans
        (congrArg Subtype.val (hfix ⟨x, hxC⟩ (by
          rw [frontier_eq_closure_inter_closure]
          exact ⟨subset_closure hxC, hx⟩)))
    · exact Equiv.Perm.subtypeCongr.right_apply _ _ hxC
  have hfcompl : ContinuousOn f (closure Cᶜ) :=
    continuousOn_id.congr hfid
  have hcover : C ∪ closure Cᶜ = univ := by
    apply eq_univ_of_univ_subset
    rw [← union_compl_self C]
    exact union_subset_union_right _ subset_closure
  have hf := hfC.union_of_isClosed hfcompl hC isClosed_closure
  rwa [hcover, continuousOn_univ] at hf

/-- Extend a frontier-fixing homeomorphism of a closed subset by the identity. -/
noncomputable def extendHomeomorphClosed {C : Set X} (hC : IsClosed C)
    (e : C ≃ₜ C) (hfix : ∀ x : C, (x : X) ∈ frontier C → e x = x) : X ≃ₜ X := by
  classical
  refine
    { e.toEquiv.subtypeCongr (Equiv.refl {x // x ∉ C}) with
      continuous_toFun := continuous_subtypeCongr_identity hC e hfix
      continuous_invFun := ?_ }
  apply continuous_subtypeCongr_identity hC e.symm
  intro x hx
  apply e.injective
  rw [e.apply_symm_apply, hfix x hx]

@[simp]
theorem extendHomeomorphClosed_apply {C : Set X} (hC : IsClosed C)
    (e : C ≃ₜ C) (hfix : ∀ x : C, (x : X) ∈ frontier C → e x = x) (x : C) :
    extendHomeomorphClosed hC e hfix x = e x := by
  classical
  exact Equiv.Perm.subtypeCongr.left_apply_subtype _ _ x

theorem extendHomeomorphClosed_eq_self {C : Set X} (hC : IsClosed C)
    (e : C ≃ₜ C) (hfix : ∀ x : C, (x : X) ∈ frontier C → e x = x)
    {x : X} (hx : x ∉ C) : extendHomeomorphClosed hC e hfix x = x := by
  classical
  exact Equiv.Perm.subtypeCongr.right_apply _ _ hx

/-- The extension fixes everything outside the interior of its closed domain. -/
theorem extendHomeomorphClosed_eq_self_of_not_mem_interior {C : Set X} (hC : IsClosed C)
    (e : C ≃ₜ C) (hfix : ∀ x : C, (x : X) ∈ frontier C → e x = x)
    {x : X} (hx : x ∉ interior C) : extendHomeomorphClosed hC e hfix x = x := by
  by_cases hxC : x ∈ C
  · have hf : x ∈ frontier C := ⟨subset_closure hxC, hx⟩
    exact (extendHomeomorphClosed_apply hC e hfix ⟨x, hxC⟩).trans
      (congrArg Subtype.val (hfix ⟨x, hxC⟩ hf))
  · exact extendHomeomorphClosed_eq_self hC e hfix hxC

/-- An embedded homeomorphism fixing the ambient frontier extends by the identity. -/
theorem exists_homeomorph_extension_of_isClosedEmbedding {f : Y → X}
    (hf : IsClosedEmbedding f) (e : Y ≃ₜ Y)
    (hfix : ∀ y, f y ∈ frontier (range f) → e y = y) :
    ∃ H : X ≃ₜ X, (∀ y, H (f y) = f (e y)) ∧
      (∀ x ∉ interior (range f), H x = x) := by
  let k : Y ≃ₜ range f := hf.isEmbedding.toHomeomorph
  let e' : range f ≃ₜ range f := (k.symm.trans e).trans k
  have he' (x : range f) (hx : (x : X) ∈ frontier (range f)) : e' x = x := by
    have hk : f (k.symm x) = x := congrArg Subtype.val (k.apply_symm_apply x)
    change k (e (k.symm x)) = x
    rw [hfix (k.symm x) (hk.symm ▸ hx), k.apply_symm_apply]
  refine ⟨extendHomeomorphClosed hf.isClosed_range e' he', ?_, ?_⟩
  · intro y
    change extendHomeomorphClosed hf.isClosed_range e' he' (k y : range f) = _
    rw [extendHomeomorphClosed_apply]
    change f (e (k.symm (k y))) = f (e y)
    rw [k.symm_apply_apply]
  · exact fun x hx => extendHomeomorphClosed_eq_self_of_not_mem_interior _ _ _ hx

/-- If the open disk has open image, the ambient frontier of the closed disk is contained in
the image of its boundary sphere. -/
theorem frontier_range_subset_image_diskSphere {n : ℕ} {f : Disk n → X}
    (hf : IsClosedEmbedding f) (hopen : IsOpen (f '' diskInterior n)) :
    frontier (range f) ⊆ f '' diskSphere n := by
  intro x hx
  obtain ⟨y, rfl⟩ := hf.isClosed_range.closure_eq ▸ hx.1
  refine ⟨y, ?_, rfl⟩
  have hy : y ∉ diskInterior n := by
    intro hy
    exact hx.2 (interior_maximal (image_subset_range f _) hopen ⟨y, hy, rfl⟩)
  have hnorm := mem_closedBall_zero_iff.mp y.property
  rw [mem_diskSphere]
  exact le_antisymm hnorm (not_lt.mp (mem_diskInterior.not.mp hy))

/-- A boundary-fixing homeomorphism of an embedded closed disk extends to the ambient space
and fixes the complement of the image of the open disk. -/
theorem exists_homeomorph_extension_disk_supported {n : ℕ} {f : Disk n → X}
    (hf : IsClosedEmbedding f) (hopen : IsOpen (f '' diskInterior n))
    (e : Disk n ≃ₜ Disk n) (hfix : ∀ y ∈ diskSphere n, e y = y) :
    ∃ H : X ≃ₜ X, (∀ y, H (f y) = f (e y)) ∧
      (∀ x ∉ f '' diskInterior n, H x = x) ∧
      (∀ s : Set (Disk n), H '' (f '' s) = f '' (e '' s)) := by
  obtain ⟨H, hH, hHfix⟩ := exists_homeomorph_extension_of_isClosedEmbedding hf e (by
    intro y hy
    obtain ⟨z, hz, heq⟩ := frontier_range_subset_image_diskSphere hf hopen hy
    exact hfix y (hf.injective heq ▸ hz))
  refine ⟨H, hH, ?_, fun s => ?_⟩
  · intro x hx
    by_cases hxf : x ∈ range f
    · obtain ⟨y, rfl⟩ := hxf
      have hy : y ∈ diskSphere n := by
        rw [mem_diskSphere]
        refine le_antisymm (mem_closedBall_zero_iff.mp y.property) ?_
        exact not_lt.mp (fun hy => hx ⟨y, mem_diskInterior.mpr hy, rfl⟩)
      rw [hH, hfix y hy]
    · exact hHfix x (fun hi => hxf (interior_subset hi))
  · rw [image_image, image_image]
    exact image_congr (fun y _ => hH y)

/-- A disk extension with support expressed using the ambient interior of the closed image. -/
theorem exists_homeomorph_extension_disk {n : ℕ} {f : Disk n → X}
    (hf : IsClosedEmbedding f) (hopen : IsOpen (f '' diskInterior n))
    (e : Disk n ≃ₜ Disk n) (hfix : ∀ y ∈ diskSphere n, e y = y) :
    ∃ H : X ≃ₜ X, (∀ y, H (f y) = f (e y)) ∧
      (∀ x ∉ interior (range f), H x = x) ∧
      (∀ s : Set (Disk n), H '' (f '' s) = f '' (e '' s)) := by
  obtain ⟨H, hH, hHfix, hHimage⟩ := exists_homeomorph_extension_disk_supported hf hopen e hfix
  refine ⟨H, hH, fun x hx => hHfix x ?_, hHimage⟩
  exact fun hxi => hx (interior_maximal (image_subset_range f _) hopen hxi)

end PoincareHighDim

end

/- Source module Submission.Topology.Cellular.CellCompression -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# Compressing a compact subset inside a closed cell

A compact subset of the open interior of a cell can be made arbitrarily small by a
homeomorphism supported in that cell. This supplies each step of the cellular shrinking
construction.
-/

namespace PoincareHighDim

open Set Metric Topology

namespace ClosedCell

variable {n : ℕ} {X : Type*} [MetricSpace X]

/-- A compact subset of the open cell can be compressed to arbitrarily small diameter,
fixing every point outside that open cell. -/
theorem exists_compression (c : ClosedCell n X) {K : Set X}
    (hK : IsCompact K) (hKC : K ⊆ c.interiorSet) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : X ≃ₜ X, (∀ x ∉ c.interiorSet, H x = x) ∧ diam (H '' K) ≤ ε := by
  obtain ⟨R, hR, hR1, hKR⟩ := c.exists_radius_of_isCompact hK hKC
  let z : Disk n := ⟨0, mem_closedBall_self zero_le_one⟩
  obtain ⟨η, hη, hηmap⟩ := Metric.continuousAt_iff.mp
    (c.isClosedEmbedding.continuous.continuousAt (x := z)) (ε / 2) (by positivity)
  let r := min (R / 2) (η / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : r < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrη : r < η := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨h, -, hsmall, hfix⟩ := exists_radial_compression_supported
    (E := EuclideanSpace ℝ (Fin n)) (δ := r / 2) (ε := r) (R := R) (S := (R + 1) / 2)
    (by positivity) (by linarith) hrR (by linarith)
  have hball (x : EuclideanSpace ℝ (Fin n)) :
      x ∈ closedBall 0 1 ↔ h x ∈ closedBall 0 1 := by
    constructor
    · intro hx
      by_contra hh
      have hn : 1 < ‖h x‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hh
      have heq : h x = x := h.injective (hfix (h x) (by linarith))
      exact hh (heq.symm ▸ hx)
    · intro hx
      by_contra hh
      have hn : 1 < ‖x‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hh
      rw [hfix x (by linarith)] at hx
      exact hh hx
  let d : Disk n ≃ₜ Disk n := h.subtype hball
  have hds (x : Disk n) (hx : x ∈ diskSphere n) : d x = x := by
    apply Subtype.ext
    change h (x : EuclideanSpace ℝ (Fin n)) = x
    apply hfix
    rw [mem_diskSphere.mp hx]
    linarith
  obtain ⟨H, hH, hHfix, -⟩ := exists_homeomorph_extension_disk
    c.isClosedEmbedding c.isOpen_interior d hds
  refine ⟨H, ?_, ?_⟩
  · intro x hx
    by_cases hxc : x ∈ c.carrier
    · have hs : x ∈ c.map '' diskSphere n := by
        rw [← c.carrier_sdiff_interiorSet]
        exact ⟨hxc, hx⟩
      obtain ⟨v, hv, rfl⟩ := hs
      rw [hH, hds v hv]
    · exact hHfix x (fun hi => hxc (interior_subset hi))
  · have hsub : H '' K ⊆ ball (c.map z) (ε / 2) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨v, -, rfl⟩ := hKC hx
      rw [hH]
      have hv : ‖(d v : EuclideanSpace ℝ (Fin n))‖ < r :=
        mem_ball_zero_iff.mp (hsmall (mem_closedBall_zero_iff.mpr (hKR v hx)))
      apply hηmap
      have hd : dist (d v) z = ‖(d v : EuclideanSpace ℝ (Fin n))‖ := by
        change dist (d v : EuclideanSpace ℝ (Fin n)) 0 = _
        exact dist_zero_right _
      rw [hd]
      exact hv.trans hrη
    have := diam_le_of_subset_closedBall (by positivity : 0 ≤ ε / 2)
      (hsub.trans ball_subset_closedBall)
    linarith

end ClosedCell

end PoincareHighDim

end

/- Source module Submission.Topology.Cellular.CellularShrinking -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# The limit of a sequence of shrinking homeomorphisms

This is the analytic part of cellular shrinking. Once homeomorphisms stabilize outside
compact sets and their images have diameter tending to zero, their uniform limit collapses
exactly the intersection of those sets. Constructing the compact cells and homeomorphisms
is a separate geometric step.
-/

namespace PoincareHighDim

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The uniform limit of compatible shrinking homeomorphisms is a continuous surjection.
Its only possible non-singleton fiber is the intersection of the shrinking sets.

The compatibility assumptions are stated for every tail of the sequence, so callers can
establish them using whichever recursive construction produces their homeomorphisms. -/
theorem exists_shrinking_limit (K : ℕ → Set X) (h : ℕ → X ≃ₜ X)
    (hcompact : ∀ i, IsCompact (K i))
    (hfixed : ∀ i j, i ≤ j → ∀ x, x ∉ K i → h j x = h i x)
    (hdiam : Tendsto (fun i => diam (h i '' K i)) atTop (𝓝 0)) :
    ∃ f : C(X, X), Function.Surjective f ∧
      TendstoUniformly (fun i => (h i : X → X)) f atTop ∧
      (∀ i x, x ∉ K i → f x = h i x) ∧
      (∀ x y, f x = f y ↔ x = y ∨ (x ∈ ⋂ i, K i) ∧ y ∈ ⋂ i, K i) := by
  classical
  have hinside : ∀ i j, i ≤ j → MapsTo (h j) (K i) (h i '' K i) := by
    intro i j hij x hx
    refine ⟨(h i).symm (h j x), ?_, (h i).apply_symm_apply _⟩
    by_contra hy
    have heq : h j ((h i).symm (h j x)) = h j x :=
      (hfixed i j hij _ hy).trans ((h i).apply_symm_apply _)
    apply hy
    rw [(h j).injective heq]
    exact hx
  let H : ℕ → C(X, X) := fun i => ⟨h i, (h i).continuous⟩
  let b : ℕ → ℝ := fun i => diam (h i '' K i)
  have hb : ∀ i, 0 ≤ b i := fun i => diam_nonneg
  have hbound : ∀ i j k, i ≤ j → i ≤ k → ∀ x,
      dist (h j x) (h k x) ≤ b i := by
    intro i j k hij hik x
    by_cases hx : x ∈ K i
    · exact dist_le_diam_of_mem ((hcompact i).image (h i).continuous).isBounded
        (hinside i j hij hx) (hinside i k hik hx)
    · rw [hfixed i j hij x hx, hfixed i k hik x hx, dist_self]
      exact hb i
  have hcauchy : CauchySeq H := by
    apply cauchySeq_iff_le_tendsto_0.mpr
    refine ⟨b, hb, ?_, hdiam⟩
    intro j k i hij hik
    exact (ContinuousMap.dist_le (hb i)).mpr (hbound i j k hij hik)
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hpoint : ∀ x, Tendsto (fun i => h i x) atTop (𝓝 (f x)) := fun x =>
    (continuous_eval_const x).tendsto f |>.comp hf
  have herror : ∀ i x, dist (f x) (h i x) ≤ b i := by
    intro i x
    apply le_of_tendsto ((hpoint x).dist tendsto_const_nhds)
    exact eventually_atTop.mpr ⟨i, fun j hij => hbound i j i hij le_rfl x⟩
  have hlimit_fixed : ∀ i x, x ∉ K i → f x = h i x := by
    intro i x hx
    apply tendsto_nhds_unique (hpoint x)
    exact tendsto_const_nhds.congr' (eventually_atTop.mpr
      ⟨i, fun j hij => (hfixed i j hij x hx).symm⟩)
  have hlimit_inside : ∀ i x, x ∈ K i → f x ∈ h i '' K i := by
    intro i x hx
    apply ((hcompact i).image (h i).continuous).isClosed.mem_of_tendsto (hpoint x)
    exact eventually_atTop.mpr ⟨i, fun j hij => hinside i j hij hx⟩
  have houtside_injective : ∀ x, x ∉ ⋂ i, K i → ∀ y, f x = f y → x = y := by
    intro x hx y hxy
    obtain ⟨i, hi⟩ : ∃ i, x ∉ K i := by simpa only [mem_iInter, not_forall] using hx
    by_cases hy : y ∈ K i
    · have hximage : h i x ∈ h i '' K i := by
        rw [← hlimit_fixed i x hi, hxy]
        exact hlimit_inside i y hy
      obtain ⟨z, hz, hzx⟩ := hximage
      exact False.elim (hi ((h i).injective hzx ▸ hz))
    · apply (h i).injective
      rwa [← hlimit_fixed i x hi, ← hlimit_fixed i y hy]
  have hcollapsed : ∀ x ∈ ⋂ i, K i, ∀ y ∈ ⋂ i, K i, f x = f y := by
    intro x hx y hy
    have hdist : ∀ i, dist (f x) (f y) ≤ b i := fun i =>
      dist_le_diam_of_mem ((hcompact i).image (h i).continuous).isBounded
        (hlimit_inside i x (mem_iInter.mp hx i))
        (hlimit_inside i y (mem_iInter.mp hy i))
    exact dist_le_zero.mp (ge_of_tendsto hdiam (Eventually.of_forall hdist))
  refine ⟨f, ?_, ContinuousMap.tendsto_iff_tendstoUniformly.mp hf, hlimit_fixed, ?_⟩
  · intro y
    have hy : Tendsto (fun i => f ((h i).symm y)) atTop (𝓝 y) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      apply squeeze_zero (fun i => dist_nonneg) _ hdiam
      intro i
      simpa using herror i ((h i).symm y)
    exact (isCompact_range f.continuous).isClosed.mem_of_tendsto hy
      (Eventually.of_forall fun i => mem_range_self ((h i).symm y))
  · intro x y
    constructor
    · intro hxy
      by_cases hx : x ∈ ⋂ i, K i
      · by_cases hy : y ∈ ⋂ i, K i
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inl (houtside_injective y hy x hxy.symm).symm
      · exact Or.inl (houtside_injective x hx y hxy)
    · rintro (rfl | ⟨hx, hy⟩)
      · rfl
      · exact hcollapsed x hx y hy

/-- For nested nonempty compact shrinking sets, the exceptional fiber exists and is exactly
their intersection. Every other fiber consists of one point. -/
theorem exists_shrinking_quotient (K : ℕ → Set X) (h : ℕ → X ≃ₜ X)
    (hcompact : ∀ i, IsCompact (K i)) (hnonempty : ∀ i, (K i).Nonempty)
    (hnested : ∀ i, K (i + 1) ⊆ K i)
    (hfixed : ∀ i j, i ≤ j → ∀ x, x ∉ K i → h j x = h i x)
    (hdiam : Tendsto (fun i => diam (h i '' K i)) atTop (𝓝 0)) :
    ∃ f : C(X, X), Function.Surjective f ∧
      TendstoUniformly (fun i => (h i : X → X)) f atTop ∧
      (∃ p, f ⁻¹' {p} = ⋂ i, K i) ∧
      (∀ x y, f x = f y ↔ x = y ∨ (x ∈ ⋂ i, K i) ∧ y ∈ ⋂ i, K i) := by
  obtain ⟨f, hsurj, hunif, -, hfiber⟩ :=
    exists_shrinking_limit K h hcompact hfixed hdiam
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K hnested hnonempty (hcompact 0) (fun i => (hcompact i).isClosed)
  refine ⟨f, hsurj, hunif, ⟨f x, ?_⟩, hfiber⟩
  ext y
  simp only [mem_preimage, mem_singleton_iff, hfiber y x]
  exact ⟨fun h => h.elim (fun hy => hy ▸ hx) And.left,
    fun hy => Or.inr ⟨hy, hx⟩⟩

/-- A recursive version: it is enough that each next homeomorphism agrees with the preceding
one off the current shrinking set. Image preservation follows from bijectivity. -/
theorem exists_shrinking_quotient_of_step (K : ℕ → Set X) (h : ℕ → X ≃ₜ X)
    (hcompact : ∀ i, IsCompact (K i)) (hnonempty : ∀ i, (K i).Nonempty)
    (hnested : ∀ i, K (i + 1) ⊆ K i)
    (hstep : ∀ i x, x ∉ K i → h (i + 1) x = h i x)
    (hdiam : Tendsto (fun i => diam (h i '' K i)) atTop (𝓝 0)) :
    ∃ f : C(X, X), Function.Surjective f ∧
      TendstoUniformly (fun i => (h i : X → X)) f atTop ∧
      (∃ p, f ⁻¹' {p} = ⋂ i, K i) ∧
      (∀ x y, f x = f y ↔ x = y ∨ (x ∈ ⋂ i, K i) ∧ y ∈ ⋂ i, K i) := by
  apply exists_shrinking_quotient K h hcompact hnonempty hnested _ hdiam
  have hmono : Antitone K := antitone_nat_of_succ_le hnested
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ j hij ih =>
    intro x hx
    rw [hstep j x (fun hxj => hx (hmono hij hxj))]
    exact ih x hx

end PoincareHighDim

end

/- Source module Submission.Topology.Cellular.CellularCollapse -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# Collapsing a cellular set

A cellular subset of a compact metric space can be collapsed to one point by a continuous
surjection of that space onto itself, with no other identifications. The construction
successively compresses the nested cells and takes the uniform limit of the resulting
homeomorphisms. This is the cellular shrinking step in Brown's proof of Schoenflies.
-/

namespace PoincareHighDim

open Set Metric Filter Topology

namespace ClosedCell

variable {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Transport a closed cell through an ambient homeomorphism. -/
def mapHomeomorph (c : ClosedCell n X) (h : X ≃ₜ Y) : ClosedCell n Y where
  map := h ∘ c.map
  isClosedEmbedding := h.isClosedEmbedding.comp c.isClosedEmbedding
  isOpen_interior := by
    rw [image_comp]
    exact h.isOpenMap _ c.isOpen_interior

@[simp]
theorem mapHomeomorph_carrier (c : ClosedCell n X) (h : X ≃ₜ Y) :
    (c.mapHomeomorph h).carrier = h '' c.carrier := by
  exact range_comp h c.map

@[simp]
theorem mapHomeomorph_interiorSet (c : ClosedCell n X) (h : X ≃ₜ Y) :
    (c.mapHomeomorph h).interiorSet = h '' c.interiorSet := by
  exact image_comp h c.map (diskInterior n)

end ClosedCell

variable {n : ℕ} {X : Type*} [MetricSpace X] [CompactSpace X]

/-- Collapse the intersection of a nested sequence of closed cells, fixing the complement
of the first open cell pointwise. -/
theorem exists_cellular_collapse_of_cells (c : ℕ → ClosedCell n X)
    (hnested : ∀ i, (c (i + 1)).carrier ⊆ (c i).interiorSet) :
    ∃ f : C(X, X), Function.Surjective f ∧
      CollapsesExactly f (⋂ i, (c i).carrier) ∧
      (∀ x ∉ (c 0).interiorSet, f x = x) := by
  classical
  have hnext (i : ℕ) (g : X ≃ₜ X) :
      ∃ g' : X ≃ₜ X,
        (∀ x ∉ (c i).interiorSet, g' x = g x) ∧
        diam (g' '' (c (i + 1)).carrier) ≤ 1 / ((i : ℝ) + 1) := by
    obtain ⟨H, hfix, hsmall⟩ := ((c i).mapHomeomorph g).exists_compression
      (((c (i + 1)).isCompact_carrier).image g.continuous)
      (by simpa only [ClosedCell.mapHomeomorph_interiorSet] using image_mono (hnested i))
      (by positivity : 0 < 1 / ((i : ℝ) + 1))
    refine ⟨g.trans H, ?_, ?_⟩
    · intro x hx
      exact hfix (g x) (by simpa using hx)
    · change diam ((H ∘ g) '' (c (i + 1)).carrier) ≤ _
      rw [image_comp]
      exact hsmall
  choose next hnext_fixed hnext_small using hnext
  let h : ℕ → X ≃ₜ X := fun i => Nat.rec (Homeomorph.refl X) next i
  have hstep : ∀ i x, x ∉ (c i).carrier → h (i + 1) x = h i x := by
    intro i x hx
    exact hnext_fixed i (h i) x (fun hi => hx ((c i).interiorSet_subset_carrier hi))
  have hmono : Antitone (fun i => (c i).carrier) := antitone_nat_of_succ_le
    (fun i => (hnested i).trans (c i).interiorSet_subset_carrier)
  have hfixed : ∀ i j, i ≤ j → ∀ x, x ∉ (c i).carrier → h j x = h i x := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ j hij ih =>
      intro x hx
      rw [hstep j x (fun hxj => hx (hmono hij hxj))]
      exact ih x hx
  have hdiam : Tendsto (fun i => diam (h i '' (c i).carrier)) atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply squeeze_zero (fun i => diam_nonneg)
      (fun i => hnext_small i (h i)) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨f, hsurj, -, hlim_fixed, hfiber⟩ := exists_shrinking_limit
    (fun i => (c i).carrier) h (fun i => (c i).isCompact_carrier) hfixed hdiam
  refine ⟨f, hsurj, hfiber, ?_⟩
  intro x hx
  rw [hlim_fixed 1 x (fun hx1 => hx (hnested 0 hx1))]
  exact hnext_fixed 0 (h 0) x hx

/-- **Cellular collapse.** A cellular set in a compact metric space can be collapsed to one
point by a continuous surjection to the same space, without any other identifications. -/
theorem IsCellular.exists_collapse {K : Set X} (hK : IsCellular n K) :
    ∃ f : C(X, X), Function.Surjective f ∧ CollapsesExactly f K := by
  obtain ⟨c, hnested, rfl⟩ := hK
  obtain ⟨f, hsurj, hfiber, -⟩ := exists_cellular_collapse_of_cells c hnested
  exact ⟨f, hsurj, hfiber⟩

/-- Collapsing a cellular set does not change the homeomorphism type of a compact metric
space. This formulation accepts any continuous surjection with precisely those fibers. -/
theorem IsCellular.nonempty_homeomorph_of_collapsesExactly {Y : Type*} [TopologicalSpace Y]
    [T2Space Y] {K : Set X} (hK : IsCellular n K) {g : X → Y}
    (hg : Continuous g) (hgs : Function.Surjective g) (hgK : CollapsesExactly g K) :
    Nonempty (X ≃ₜ Y) := by
  obtain ⟨f, hfs, hfK⟩ := hK.exists_collapse
  exact PoincareHighDim.nonempty_homeomorph_of_collapsesExactly
    f.continuous hfs hg hgs hfK hgK

end PoincareHighDim

end

/- Source module Submission.Topology.Recognition.TwoOpenCells -/
section
/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/


/-!
# A compact space covered by two open cells is a sphere

Collapse the complement of one chart to infinity. The other chart contains a closed cell
neighborhood of the exceptional fiber, so the one-fiber criterion proves that fiber
cellular. Cellular quotient recognition then identifies the original space with the sphere.
-/

namespace PoincareHighDim

open Set Metric Topology

/-- **Brown's two-open-cells theorem.** A compact metric space covered by two open
Euclidean `n`-cells, for `n ≥ 1`, is homeomorphic to the standard `n`-sphere. -/
theorem nonempty_homeomorph_sphere_of_two_open_cells {n : ℕ} (hn : 1 ≤ n)
    {X : Type*} [MetricSpace X] [CompactSpace X]
    {φ₀ φ₁ : EuclideanSpace ℝ (Fin n) → X}
    (hφ₀ : IsOpenEmbedding φ₀) (hφ₁ : IsOpenEmbedding φ₁)
    (hcover : range φ₀ ∪ range φ₁ = univ) :
    Nonempty (X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hproper {φ : EuclideanSpace ℝ (Fin n) → X} (hφ : IsOpenEmbedding φ) :
      range φ ≠ univ := by
    intro heq
    apply noncompact_univ (EuclideanSpace ℝ (Fin n))
    apply hφ.isEmbedding.isCompact_iff.mpr
    rw [image_univ, heq]
    exact isCompact_univ
  obtain ⟨f₀, hfs₀, hfK₀, -, -⟩ := exists_collapse_of_openEmbedding hφ₀ (hproper hφ₀)
  let H : OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  let f := H ∘ f₀
  have hf : Continuous f := H.continuous.comp f₀.continuous
  have hfs : Function.Surjective f := H.surjective.comp hfs₀
  let K := (range φ₀)ᶜ
  have hfK : CollapsesExactly f K := hfK₀.comp_injective H.injective
  have hK : IsCompact K := hφ₀.isOpen_range.isClosed_compl.isCompact
  have hKne : K.Nonempty := nonempty_compl.mpr (hproper hφ₀)
  have hKφ₁ : K ⊆ range φ₁ := by
    intro x hx
    have hxcover : x ∈ range φ₀ ∪ range φ₁ := hcover ▸ mem_univ x
    exact hxcover.resolve_left hx
  obtain ⟨c, hKc, hcφ₁⟩ := exists_closedCell_in_openEmbedding hφ₁ hK hKφ₁
  let K' := c.map ⁻¹' K
  let F := f ∘ c.map
  have hF : Continuous F := hf.comp c.isClosedEmbedding.continuous
  have hFK : CollapsesExactly F K' := by
    intro x y
    simpa only [F, K', Function.comp_apply, mem_preimage,
      c.isClosedEmbedding.injective.eq_iff] using hfK (c.map x) (c.map y)
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hK' : IsCompact K' := (hK.isClosed.preimage c.isClosedEmbedding.continuous).isCompact
  have hK'ne : K'.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨y, hy⟩ := c.interiorSet_subset_carrier (hKc hx)
    refine ⟨y, ?_⟩
    change c.map y ∈ K
    rwa [hy]
  have hK'I : K' ⊆ diskInterior n := by
    intro x hx
    exact c.isClosedEmbedding.injective.mem_set_image.mp (hKc hx)
  have hFproper : range F ≠ univ := by
    intro hall
    obtain ⟨x, hx⟩ := nonempty_compl.mpr (hproper hφ₁)
    obtain ⟨y, hy⟩ : f x ∈ range F := hall ▸ mem_univ _
    rcases (hfK (c.map y) x).mp hy with heq | ⟨-, hxK⟩
    · exact hx (heq ▸ hcφ₁ (mem_range_self y))
    · exact hx (hKφ₁ hxK)
  have hFI : IsOpen (F '' diskInterior n) := by
    change IsOpen ((f ∘ c.map) '' diskInterior n)
    rw [image_comp]
    apply isOpen_image_of_saturated hf c.isOpen_interior isOpen_univ (subset_univ _)
      (by rw [hfs.range_eq])
    intro x y hxy hx
    rcases (hfK x y).mp hxy with rfl | ⟨-, hy⟩
    · exact hx
    · exact hKc hy
  have hcell := c.isCellular_image_of_collapsesExactly_sphere
    hF hFK hK' hK'ne hK'I hFproper hFI
  have hKimage : c.map '' K' = K :=
    image_preimage_eq_of_subset (hKc.trans c.interiorSet_subset_carrier)
  rw [hKimage] at hcell
  exact hcell.nonempty_homeomorph_of_collapsesExactly hf hfs hfK

end PoincareHighDim

end

open Set Metric Topology in
theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R2.H2 := by
  intro n hn X _ _ u v hu hv cover
  exact PoincareHighDim.nonempty_homeomorph_sphere_of_two_open_cells hn hu hv cover

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
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

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
