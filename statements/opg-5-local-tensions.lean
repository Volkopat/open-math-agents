import Mathlib

/-!
# 5-local-tensions

Source https://www.openproblemgarden.org/op/5_local_tensions

There is a uniform edge-width threshold above which every loopless graph
embedded in a surface admits an integer 5-local-tension.
-/

namespace OMA.S_opg_5_local_tensions

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def startVertex {V E : Type} (src dst : E → V) (e : E) (reverse : Bool) : V :=
  if reverse then dst e else src e

def endVertex {V E : Type} (src dst : E → V) (e : E) (reverse : Bool) : V :=
  if reverse then src e else dst e

/-- An undirected walk with the traversal direction recorded at each edge. -/
inductive Walk {V E : Type} (src dst : E → V) : V → V → Type
  | nil (v : V) : Walk src dst v v
  | step (e : E) (reverse : Bool) {v : V}
      (tail : Walk src dst (endVertex src dst e reverse) v) :
      Walk src dst (startVertex src dst e reverse) v

variable {V E S : Type} [TopologicalSpace S]

structure Embedding (V E S : Type) [TopologicalSpace S] where
  src : E → V
  dst : E → V
  loopless : ∀ e, src e ≠ dst e
  vertex : V ↪ S
  arc : ∀ e, Path (vertex (src e)) (vertex (dst e))
  arc_injective : ∀ e, Function.Injective (arc e)
  vertex_on_arc : ∀ v e t, vertex v = arc e t → v = src e ∨ v = dst e
  intersection_at_vertex : ∀ e f, e ≠ f → ∀ s t, arc e s = arc f t →
    ∃ v, arc e s = vertex v

variable {src dst : E → V}

def Walk.edges {u v : V} (w : Walk src dst u v) : List E :=
  match w with
  | .nil _ => []
  | .step e _ tail => e :: tail.edges

def Walk.verticesBeforeEnd {u v : V} (w : Walk src dst u v) : List V :=
  match w with
  | .nil _ => []
  | .step e reverse tail => startVertex src dst e reverse :: tail.verticesBeforeEnd

def Walk.height {u v : V} (weight : E → ℤ) (w : Walk src dst u v) : ℤ :=
  match w with
  | .nil _ => 0
  | .step e reverse tail => (if reverse then -weight e else weight e) + tail.height weight

def Embedding.traverse (G : Embedding V E S) (e : E) (reverse : Bool) :
    Path (G.vertex (startVertex G.src G.dst e reverse))
      (G.vertex (endVertex G.src G.dst e reverse)) :=
  match reverse with
  | false => G.arc e
  | true => (G.arc e).symm

/-- Concatenate the embedded edge paths in their traversal directions. -/
noncomputable def Walk.toPath (G : Embedding V E S) {u v : V} (w : Walk G.src G.dst u v) :
    Path (G.vertex u) (G.vertex v) :=
  match w with
  | .nil x => Path.refl (G.vertex x)
  | .step e reverse tail => (G.traverse e reverse).trans (tail.toPath G)

def IsContractible (G : Embedding V E S) {u : V} (w : Walk G.src G.dst u u) : Prop :=
  (w.toPath G).Homotopic (Path.refl (G.vertex u))

def HasEdgeWidthAtLeast (G : Embedding V E S) (c : ℕ) : Prop :=
  ∀ (u : V) (w : Walk G.src G.dst u u),
    0 < w.edges.length → w.edges.length < c →
    w.edges.Nodup → w.verticesBeforeEnd.Nodup → IsContractible G w

def HasFiveLocalTension (G : Embedding V E S) : Prop :=
  ∃ weight : E → ℤ, (∀ e, 0 < |weight e| ∧ |weight e| < 5) ∧
    ∀ (u : V) (w : Walk G.src G.dst u u), IsContractible G w → w.height weight = 0

theorem main :
    ∃ c : ℕ, ∀ (S V E : Type)
      [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
      [CompactSpace S] [ConnectedSpace S] [ChartedSpace Plane S]
      [Finite V] [Finite E] (G : Embedding V E S),
      HasEdgeWidthAtLeast G c → HasFiveLocalTension G := by
  sorry

end OMA.S_opg_5_local_tensions
