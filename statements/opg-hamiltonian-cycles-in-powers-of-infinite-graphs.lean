import Mathlib

/-!
# Hamiltonian cycles in powers of infinite graphs

Source https://www.openproblemgarden.org/op/hamiltonian_cycles_in_powers_of_infinite_graphs

The cube of a countable connected graph and the square of a countable
2-connected graph are conjectured to have Hamilton circles. We use the
end topology specified in Sections 2 and 8 of Georgakopoulos,
Infinite Hamilton cycles in squares of locally finite graphs.
-/

namespace OMA.S_opg_hamiltonian_cycles_in_powers_of_infinite_graphs

variable {V : Type}

structure Ray (G : SimpleGraph V) where
  vertex : ℕ ↪ V
  consecutive : ∀ n, G.Adj (vertex n) (vertex (n + 1))

def componentAfterDeletion (G : SimpleGraph V) (removed : Finset V) (root : V) : Set V :=
  {v | ∃ w : G.Walk root v, ∀ x ∈ w.support, x ∉ removed}

def Ray.HasTailIn {G : SimpleGraph V} (r : Ray G) (C : Set V) : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, r.vertex n ∈ C

def SameEnd {G : SimpleGraph V} (r s : Ray G) : Prop :=
  ∀ removed : Finset V, ∃ root : V, root ∉ removed ∧
    r.HasTailIn (componentAfterDeletion G removed root) ∧
    s.HasTailIn (componentAfterDeletion G removed root)

abbrev End (G : SimpleGraph V) := Quot (@SameEnd V G)

variable [LinearOrder V]

abbrev Edge (G : SimpleGraph V) := {p : V × V // p.1 < p.2 ∧ G.Adj p.1 p.2}
abbrev OpenUnitInterval := Set.Ioo (0 : ℝ) 1

inductive Point (G : SimpleGraph V)
  | vertex (v : V)
  | interior (e : Edge G) (t : OpenUnitInterval)
  | endPoint (ω : End G)

variable {G : SimpleGraph V}

def openEdgeInterval (e : Edge G) (a b : ℝ) : Set (Point G) :=
  {p | ∃ t : OpenUnitInterval, p = .interior e t ∧ a < t.val ∧ t.val < b}

def vertexNeighborhood (v : V) (ε : Edge G → OpenUnitInterval) : Set (Point G) :=
  {p | match p with
    | .vertex w => w = v
    | .interior e t =>
        (e.val.1 = v ∧ t.val < (ε e).val) ∨
        (e.val.2 = v ∧ 1 - (ε e).val < t.val)
    | .endPoint _ => False}

def endNeighborhood (removed : Finset V) (root : V)
    (ε : Edge G → OpenUnitInterval) : Set (Point G) :=
  let C := componentAfterDeletion G removed root
  {p | match p with
    | .vertex v => v ∈ C
    | .interior e t =>
        (e.val.1 ∈ C ∧ e.val.2 ∈ C) ∨
        (e.val.1 ∈ C ∧ e.val.2 ∈ removed ∧ t.val < (ε e).val) ∨
        (e.val.2 ∈ C ∧ e.val.1 ∈ removed ∧ 1 - (ε e).val < t.val)
    | .endPoint ω => ∃ r : Ray G, Quot.mk (@SameEnd V G) r = ω ∧ r.HasTailIn C}

abbrev graphEndTopology (G : SimpleGraph V) : TopologicalSpace (Point G) :=
  TopologicalSpace.generateFrom
    {U | (∃ (e : Edge G) (a b : ℝ), U = openEdgeInterval e a b) ∨
      (∃ (v : V) (ε : Edge G → OpenUnitInterval), U = vertexNeighborhood v ε) ∨
      ∃ (removed : Finset V) (root : V) (ε : Edge G → OpenUnitInterval),
        root ∉ removed ∧ (∃ r : Ray G, r.HasTailIn (componentAfterDeletion G removed root)) ∧
          U = endNeighborhood removed root ε}

def HasHamiltonCircle (G : SimpleGraph V) : Prop :=
  letI : TopologicalSpace (Point G) := graphEndTopology G
  ∃ C : Set (Point G), (∀ v : V, Point.vertex v ∈ C) ∧
    Nonempty ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ≃ₜ C)

noncomputable def graphPower (G : SimpleGraph V) (k : ℕ) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => G.edist u v ≤ k)

def IsTwoConnected (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ v : V, (G.induce ({v} : Set V)ᶜ).Connected

theorem main :
    ∀ (V : Type) [Countable V] [LinearOrder V] (G : SimpleGraph V),
      Nonempty (Fin 3 ↪ V) →
      (G.Connected → HasHamiltonCircle (graphPower G 3)) ∧
      (IsTwoConnected G → HasHamiltonCircle (graphPower G 2)) := by
  sorry

end OMA.S_opg_hamiltonian_cycles_in_powers_of_infinite_graphs
