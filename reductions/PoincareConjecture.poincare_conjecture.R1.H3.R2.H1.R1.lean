import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R2
import Mathlib

/-!
Separate the connected Hamilton–Cairns smoothing theorem into:
* `H1`: finite locally flat geometric triangulation of a compact connected topological 3-manifold;
* `H2`: construction of a covering family of smooth Euclidean coordinate neighborhoods on the
  geometric realization `K.space` of such a triangulation.

In `main`, coordinate charts on `K.space` are pulled back along `e : M ≃ₜ K.space` using
`Homeomorph.transOpenPartialHomeomorph`; transition maps are shown to agree identically with the
charts on `K.space`, and the resulting smooth family is assembled into a compatible
`ChartedSpace (EuclideanSpace ℝ (Fin 3)) M` satisfying `IsManifold (𝓡 3) ∞ M`.
Adapted in part from `AtlasTransport.lean` and `AtlasOfCover.lean` in
`frenzymath/PoincareConjecture` (`62db01af`, Apache-2.0).
-/

open Set Geometry TopologicalSpace
open scoped Manifold ContDiff Topology

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R2_H1_R1

private theorem pullback_chart_transition {H M N : Type*} [TopologicalSpace H]
    [TopologicalSpace M] [TopologicalSpace N] (e : M ≃ₜ N)
    (c d : OpenPartialHomeomorph N H) :
    (e.transOpenPartialHomeomorph c).symm.trans (e.transOpenPartialHomeomorph d) =
      c.symm.trans d := by
  apply OpenPartialHomeomorph.ext
  · intro x
    change d (e (e.symm (c.symm x))) = d (c.symm x)
    rw [e.apply_symm_apply]
  · intro x
    change c (e (e.symm (d.symm x))) = c (d.symm x)
    rw [e.apply_symm_apply]
  · ext x
    change (x ∈ c.target ∧ e (e.symm (c.symm x)) ∈ d.source) ↔
      (x ∈ c.target ∧ c.symm x ∈ d.source)
    rw [e.apply_symm_apply]

private theorem exists_smooth_atlas_of_cover {ι M : Type*} [TopologicalSpace M]
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (hcompat : ∀ i j, ContDiffOn ℝ ∞ ((c i).symm.trans (c j))
      ((c i).symm.trans (c j)).source) :
    ∃ a : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := a
      IsManifold (𝓡 3) ∞ M := by
  classical
  let a : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M :=
    { atlas := Set.range c
      chartAt := fun x => c (Classical.choose (hcover x))
      mem_chart_source := fun x => Classical.choose_spec (hcover x)
      chart_mem_atlas := fun x => ⟨Classical.choose (hcover x), rfl⟩ }
  refine ⟨a, ?_⟩
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := a
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa only [mfld_simps] using hcompat i j

def H1 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ConnectedSpace M],
    ∃ n : ℕ,
      let E := EuclideanSpace ℝ (Fin n)
      letI : DecidableEq E := Classical.decEq E
      ∃ K : SimplicialComplex ℝ E,
        let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
        let star (p : E) := {t | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}
        let carrier (faces : Set (Finset E)) := ⋃ t ∈ faces, convexHull ℝ (t : Set E)
        K.faces.Finite ∧
        (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) ∧
        (∀ t ∈ K.faces, t.card = 2 → IsConnected (carrier (link t))) ∧
        (∀ t ∈ K.faces, t.card = 3 → ({q : E | {q} ∈ link t} : Set E).ncard = 2) ∧
        (∀ p : E, {p} ∈ K.faces →
          ∃ f : E → EuclideanSpace ℝ (Fin 3),
            (∀ s ∈ star p, ∃ a : E →ᴬ[ℝ] EuclideanSpace ℝ (Fin 3),
              EqOn f a (convexHull ℝ (s : Set E))) ∧
            InjOn f (carrier (star p)) ∧ (interior (f '' carrier (star p))).Nonempty) ∧
        Nonempty (M ≃ₜ K.space)

def H2 : Prop :=
  ∀ n : ℕ,
    let E := EuclideanSpace ℝ (Fin n)
    letI : DecidableEq E := Classical.decEq E
    ∀ K : SimplicialComplex ℝ E,
      let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
      let star (p : E) := {t | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}
      let carrier (faces : Set (Finset E)) := ⋃ t ∈ faces, convexHull ℝ (t : Set E)
      K.faces.Finite →
      (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) →
      (∀ t ∈ K.faces, t.card = 2 → IsConnected (carrier (link t))) →
      (∀ t ∈ K.faces, t.card = 3 → ({q : E | {q} ∈ link t} : Set E).ncard = 2) →
      (∀ p : E, {p} ∈ K.faces →
        ∃ f : E → EuclideanSpace ℝ (Fin 3),
          (∀ s ∈ star p, ∃ a : E →ᴬ[ℝ] EuclideanSpace ℝ (Fin 3),
            EqOn f a (convexHull ℝ (s : Set E))) ∧
          InjOn f (carrier (star p)) ∧ (interior (f '' carrier (star p))).Nonempty) →
      ∃ (ι : Type) (c : ι → OpenPartialHomeomorph K.space (EuclideanSpace ℝ (Fin 3))),
        (∀ x : K.space, ∃ i : ι, x ∈ (c i).source) ∧
        ∀ i j : ι, ContDiffOn ℝ ∞ ((c i).symm.trans (c j))
          ((c i).symm.trans (c j)).source

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R2.H1 := by
  intro hTri hCoord M _ _ _ _ _ _
  obtain ⟨n, K, hfin, hpure, hedge, htri, hbrouwer, ⟨e⟩⟩ := hTri M
  obtain ⟨ι, c, hcover, hcompat⟩ := hCoord n K hfin hpure hedge htri hbrouwer
  refine exists_smooth_atlas_of_cover (fun i => e.transOpenPartialHomeomorph (c i)) ?_ ?_
  · intro x
    obtain ⟨i, hi⟩ := hcover (e x)
    exact ⟨i, hi⟩
  · intro i j
    rw [pullback_chart_transition e (c i) (c j)]
    exact hcompat i j

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R2_H1_R1
