import Mathlib

/-!
# Unit vector flows

Source: https://www.openproblemgarden.org/op/unit_vector_flows
Credit: @shc261392

Conjecture (Jain): for every graph `G` without a bridge, there is a flow
`φ : E(G) → S² = {x ∈ ℝ³ : |x| = 1}`.

(The source also states a second conjecture, on maps `q : S² → {±1, ±2, ±3, ±4}`; together the
two imply Tutte's 5-flow conjecture. Only the first, the title conjecture, is stated here.)

Reading used here:
* `G` is a finite multigraph with a fixed orientation: a finite vertex type `V`, a finite edge
  type `E` and `src tgt : E → V` (loops and parallel edges allowed). Reversing an edge and
  negating its value preserves the flow condition and keeps values in `S²`, so the existence of
  an `S²`-flow does not depend on the orientation.
* An edge `e` is a bridge if its ends are not joined by a path in the underlying undirected
  graph avoiding `e`.
* A flow is `φ : E → ℝ³` with, at each vertex, the sum over entering edges equal to the sum over
  leaving edges; it is an `S²`-flow when every value has norm `1`.
-/

namespace OMA.S_opg_unit_vector_flows

/-- No edge is a bridge in the underlying undirected multigraph. -/
def Bridgeless {V E : Type} (src tgt : E → V) : Prop :=
  ∀ e, Relation.ReflTransGen
    (fun a b => ∃ e', e' ≠ e ∧ ((src e' = a ∧ tgt e' = b) ∨ (src e' = b ∧ tgt e' = a)))
    (src e) (tgt e)

theorem main :
    ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (src tgt : E → V),
      Bridgeless src tgt →
        ∃ φ : E → EuclideanSpace ℝ (Fin 3), (∀ e, ‖φ e‖ = 1) ∧
          ∀ v : V, ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), φ e =
            ∑ e ∈ Finset.univ.filter (fun e => src e = v), φ e := by
  sorry

end OMA.S_opg_unit_vector_flows
