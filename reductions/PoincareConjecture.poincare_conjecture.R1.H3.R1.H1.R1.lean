import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R1

/-!
The finite triangulation step reduces to the connected case and closure of the
required geometric triangulations under finite topological disjoint unions.
A compact locally connected manifold is the finite disjoint union of its
clopen connected components, each with the induced manifold charts.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H1_R1

open Geometry Set Topology

def H1 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M],
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
  let Triangulates (X : Type) [TopologicalSpace X] : Prop :=
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
        Nonempty (X ≃ₜ K.space)
  ∀ (ι : Type) [Finite ι] (X : ι → Type) [∀ i, TopologicalSpace (X i)],
    (∀ i, Triangulates (X i)) → Triangulates (Σ i, X i)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1.H1 := by
  intro triangulate assemble M _ _ _ _ _
  have : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let F (c : ConnectedComponents M) : Set M := ConnectedComponents.mk ⁻¹' {c}
  have hopen (c : ConnectedComponents M) : IsOpen (F c) := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simpa only [F, connectedComponents_preimage_singleton] using
      (isOpen_connectedComponent (x := x))
  have each (c : ConnectedComponents M) := by
    have hconn : IsConnected (F c) := by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      simpa only [F, connectedComponents_preimage_singleton] using
        (isConnected_connectedComponent (x := x))
    have hclosed : IsClosed (F c) := by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      simpa only [F, connectedComponents_preimage_singleton] using
        (isClosed_connectedComponent (x := x))
    have : ConnectedSpace (F c) := isConnected_iff_connectedSpace.mp hconn
    have : CompactSpace (F c) := isCompact_iff_compactSpace.mp hclosed.isCompact
    let U : TopologicalSpace.Opens M := ⟨F c, hopen c⟩
    let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (F c) :=
      (inferInstance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) U)
    exact triangulate (F c)
  let e : (Σ c : ConnectedComponents M, F c) ≃ₜ M :=
    (Equiv.sigmaFiberEquiv ConnectedComponents.mk).toHomeomorphOfContinuousOpen
      (continuous_sigma fun _ ↦ continuous_subtype_val)
      (isOpenMap_sigma.mpr fun c ↦ (hopen c).isOpenEmbedding_subtypeVal.isOpenMap)
  obtain ⟨n, K, hfinite, hpure, hedge, htriangle, hstar, ⟨h⟩⟩ :=
    assemble (ConnectedComponents M) (fun c ↦ F c) each
  exact ⟨n, K, hfinite, hpure, hedge, htriangle, hstar, ⟨e.symm.trans h⟩⟩

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H1_R1
