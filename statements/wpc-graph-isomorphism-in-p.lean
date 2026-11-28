import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Encoding
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Is graph isomorphism in P?

Source: https://en.wikipedia.org/wiki/Graph_isomorphism_problem
Credit: @hadijannat

States the open question of whether the Graph Isomorphism problem belongs to the complexity
class P: is there a deterministic polynomial-time Turing machine (`Turing.TM2ComputableInPolyTime`)
that decides whether two finite simple graphs `(G₁, G₂)` are isomorphic?

Conventions:
* A finite graph is represented as `SimpleGraph (Fin n)` packaged with its vertex count `n : ℕ`.
* `encodeGraph` encodes `(n, G)` as the self-delimiting binary representation of `n` followed
  by the row-major `n × n` adjacency matrix over `Bool`.
* `encodeGraphPair` encodes a pair `(G₁, G₂)` using self-delimiting framing (`delimit`),
  matching the `BitstringEncoding` conventions of `formal-conjectures`.
* `main` asserts the affirmative answer (GI ∈ P).
-/

namespace OMA.S_wpc_graph_isomorphism_in_p

/-- A finite simple graph on vertices `Fin n`. -/
structure FiniteGraph where
  n : ℕ
  graph : SimpleGraph (Fin n)

/-- Self-delimiting bitstring framing: each bit `b` becomes `[true, b]`, terminated by `false`. -/
def delimit : List Bool → List Bool
  | [] => [false]
  | b :: l => true :: b :: delimit l

/-- Row-major `n × n` adjacency matrix bits for a finite graph. -/
noncomputable def adjBits (G : FiniteGraph) : List Bool := by
  classical
  exact (List.finRange G.n).flatMap fun u =>
    (List.finRange G.n).map fun v => decide (G.graph.Adj u v)

/-- Canonical bitstring encoding of a finite graph `(n, G)`. -/
noncomputable def encodeGraph (G : FiniteGraph) : List Bool :=
  delimit (Computability.encodeNat G.n) ++ adjBits G

/-- Self-delimiting bitstring encoding of a pair of finite graphs. -/
noncomputable def encodeGraphPair (p : FiniteGraph × FiniteGraph) : List Bool :=
  delimit (encodeGraph p.1) ++ encodeGraph p.2

/-- Singleton bitstring encoding of a boolean decision output. -/
def encodeBool (b : Bool) : List Bool := [b]

/-- Decision predicate for graph isomorphism on pairs of finite graphs. -/
noncomputable def isIsomorphic (p : FiniteGraph × FiniteGraph) : Bool := by
  classical
  exact decide (Nonempty (SimpleGraph.Iso p.1.graph p.2.graph))

theorem main :
    Nonempty (Turing.TM2ComputableInPolyTime encodeGraphPair encodeBool isIsomorphic) := by
  sorry

end OMA.S_wpc_graph_isomorphism_in_p
