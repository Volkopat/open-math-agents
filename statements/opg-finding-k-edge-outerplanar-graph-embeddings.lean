import Mathlib

namespace OMA.S_opg_finding_k_edge_outerplanar_graph_embeddings

abbrev GraphInput := Σ n : ℕ, SimpleGraph (Fin n)

/-- A traversal step around a face reverses a dart and then rotates at its new tail. -/
def faceSuccessor {n : ℕ} {G : SimpleGraph (Fin n)}
    (rotation : Equiv.Perm G.Dart) : Equiv.Perm G.Dart :=
  (⟨SimpleGraph.Dart.symm, SimpleGraph.Dart.symm,
    SimpleGraph.Dart.symm_involutive, SimpleGraph.Dart.symm_involutive⟩ :
      Equiv.Perm G.Dart).trans rotation

abbrev Face {n : ℕ} {G : SimpleGraph (Fin n)} (rotation : Equiv.Perm G.Dart) :=
  Quot (faceSuccessor rotation).SameCycle

/-- The face on the side indicated by an oriented edge. -/
def faceOf {n : ℕ} {G : SimpleGraph (Fin n)}
    (rotation : Equiv.Perm G.Dart) (d : G.Dart) : Face rotation :=
  Quot.mk _ d

/-- A spherical rotation system with one designated outer face per component with edges. -/
def IsPlaneLayout {n : ℕ} {G : SimpleGraph (Fin n)}
    (rotation : Equiv.Perm G.Dart) (outer : Set (Face rotation)) : Prop :=
  (∀ d e, rotation.SameCycle d e ↔ d.fst = e.fst) ∧
    n + Nat.card (Face rotation) + Nat.card {v : Fin n // ∀ w, ¬ G.Adj v w} =
      Nat.card G.edgeSet + 2 * Nat.card G.ConnectedComponent ∧
    (∀ d : G.Dart, ∃! f : Face rotation,
      f ∈ outer ∧ ∃ e : G.Dart, G.Reachable d.fst e.fst ∧ faceOf rotation e = f)

/-- Faces are adjacent across an edge whenever the two sides are different faces. -/
def faceGraph {n : ℕ} {G : SimpleGraph (Fin n)} (rotation : Equiv.Perm G.Dart) :
    SimpleGraph (Face rotation) :=
  SimpleGraph.fromRel (fun f g => ∃ d : G.Dart, faceOf rotation d = f ∧ faceOf rotation d.symm = g)

/-- An edge is removed by round k if one incident face is reached in fewer than k dual steps. -/
def PeelsWithin {n : ℕ} {G : SimpleGraph (Fin n)}
    (rotation : Equiv.Perm G.Dart) (outer : Set (Face rotation)) (k : ℕ) : Prop :=
  ∀ d : G.Dart, ∃ f ∈ outer,
    (faceGraph rotation).edist f (faceOf rotation d) < (k : ENat) ∨
      (faceGraph rotation).edist f (faceOf rotation d.symm) < (k : ENat)

/-- A binary numeral followed by a separator. -/
def encodeNatField (n : ℕ) : List Computability.Γ' :=
  (Computability.encodeNat n).map Computability.Γ'.bit ++ [.comma]

/-- The vertex count followed by the adjacency matrix in row order. -/
noncomputable def encodeGraph (input : GraphInput) : List Computability.Γ' := by
  classical
  exact encodeNatField input.1 ++
    (List.ofFn fun v : Fin input.1 =>
      List.ofFn fun w : Fin input.1 => Computability.Γ'.bit (decide (input.2.Adj v w))).flatten

/-- The number of rounds and a table giving for each dart its successor and outer-face flag. -/
noncomputable def layoutCode {n : ℕ} {G : SimpleGraph (Fin n)}
    (rotation : Equiv.Perm G.Dart) (outer : Set (Face rotation)) (k : ℕ) : List ℕ := by
  classical
  exact k :: (List.ofFn fun v : Fin n =>
    List.ofFn fun w : Fin n =>
      if h : G.Adj v w then
        let d : G.Dart := ⟨(v, w), h⟩
        2 * ((rotation d).snd.val + 1) + if faceOf rotation d ∈ outer then 1 else 0
      else 0).flatten

/-- A code for a plane embedding with the least possible number of peeling rounds. -/
def IsOptimalCode (input : GraphInput) (output : List ℕ) : Prop :=
  ∃ (rotation : Equiv.Perm input.2.Dart) (outer : Set (Face rotation)) (k : ℕ),
    IsPlaneLayout rotation outer ∧ PeelsWithin rotation outer k ∧
      (∀ (rotation' : Equiv.Perm input.2.Dart) (outer' : Set (Face rotation')) (k' : ℕ),
        IsPlaneLayout rotation' outer' →
        PeelsWithin rotation' outer' k' → k ≤ k') ∧
      output = layoutCode rotation outer k

/-- A minimum-edge-outerplanarity embedding can be found in polynomial time. -/
theorem main :
    ∃ solve : GraphInput → List ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime encodeGraph
        (fun output : List ℕ => output.flatMap encodeNatField) solve) ∧
      ∀ input : GraphInput,
        (∃ (rotation : Equiv.Perm input.2.Dart) (outer : Set (Face rotation)),
          IsPlaneLayout rotation outer) →
        IsOptimalCode input (solve input) := by
  sorry

end OMA.S_opg_finding_k_edge_outerplanar_graph_embeddings
