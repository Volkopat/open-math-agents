import Mathlib

namespace OMA.S_opg_what_is_the_largest_graph_of_positive_curvature

open scoped BigOperators

/-- The boundary successor first reverses the dart and then rotates at its new vertex. -/
def faceSuccessor {n : ℕ} {G : SimpleGraph (Fin n)}
    (rotation : Equiv.Perm G.Dart) : Equiv.Perm G.Dart :=
  (⟨SimpleGraph.Dart.symm, SimpleGraph.Dart.symm,
    SimpleGraph.Dart.symm_involutive, SimpleGraph.Dart.symm_involutive⟩ :
      Equiv.Perm G.Dart).trans rotation

/-- The size of the face incident to a dart, counting its boundary steps. -/
noncomputable def faceSize {n : ℕ} {G : SimpleGraph (Fin n)}
    (rotation : Equiv.Perm G.Dart) (d : G.Dart) : ℕ :=
  Nat.card {e : G.Dart // (faceSuccessor rotation).SameCycle d e}

/-- Each dart leaving the vertex contributes its face incidence, with multiplicity. -/
noncomputable def curvature {n : ℕ} {G : SimpleGraph (Fin n)}
    (rotation : Equiv.Perm G.Dart) (v : Fin n) : ℚ := by
  classical
  exact 1 - (Nat.card (G.neighborSet v) : ℚ) / 2 +
    ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v), (faceSize rotation d : ℚ)⁻¹

/-- The graph of an antiprism is the square of a cycle on twice its order. -/
def antiprismGraph (k : ℕ) : SimpleGraph (Fin (2 * k)) :=
  SimpleGraph.fromRel (fun a b => (b - a).val ≤ 2)

/-- A spherical map of strictly positive curvature outside the two exceptional families. -/
def IsPCC {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.Connected ∧ (∀ v, 3 ≤ Nat.card (G.neighborSet v)) ∧
    (∀ k ≥ 3,
      ¬ Nonempty (G ≃g (SimpleGraph.cycleGraph k).boxProd (⊤ : SimpleGraph (Fin 2))) ∧
      ¬ Nonempty (G ≃g antiprismGraph k)) ∧
    ∃ rotation : Equiv.Perm G.Dart,
      (∀ d e, rotation.SameCycle d e ↔ d.fst = e.fst) ∧
      n + Nat.card (Quot (faceSuccessor rotation).SameCycle) = Nat.card G.edgeSet + 2 ∧
      (∀ d, 3 ≤ faceSize rotation d) ∧
      (∀ v, 0 < curvature rotation v)

/-- The largest planar graph of everywhere positive combinatorial curvature has 208
vertices under the minimum degree hypotheses and prism and antiprism exclusions. -/
theorem main :
    IsGreatest {n : ℕ | ∃ G : SimpleGraph (Fin n), IsPCC G} 208 := by
  sorry

end OMA.S_opg_what_is_the_largest_graph_of_positive_curvature
