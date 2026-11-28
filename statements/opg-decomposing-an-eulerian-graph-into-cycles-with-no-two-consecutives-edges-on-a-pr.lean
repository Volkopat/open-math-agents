import Mathlib

/-!
# Decomposing an eulerian graph into cycles with no two consecutive edges on a prescribed
eulerian tour

Source: https://www.openproblemgarden.org/op/decomposing_an_eulerian_graph_into_cycles_with_no_two_consecutives_edges_on_a_prescirbed_eulerian_tour
Credit: @shc261392

Conjecture (Sabidussi's compatibility conjecture): let `G` be an eulerian graph of minimum
degree 4, and let `W` be an eulerian tour of `G`. Then `G` admits a decomposition into cycles
none of which contains two consecutive edges of `W`.

Reading used here:
* `G` is a finite loopless multigraph: a finite vertex type `V`, a finite edge type `E`, and
  `ends : E → Sym2 V` with no loops; every vertex meets at least four edges.
* An eulerian tour is a closed walk using every edge exactly once: an enumeration
  `τ : Fin m ≃ E` of the edges together with vertices `w : Fin m → V` such that edge `τ i` joins
  `w i` and `w (i+1)` (indices mod `m`, via `finRotate`). Its consecutive edges are
  `τ i, τ (i+1)`, cyclically. (The existence of the tour makes `G` eulerian.)
* A cycle is (the edge set of) a minimal nonempty even edge set; in a loopless multigraph these
  are exactly the edge sets of cycles, 2-cycles of parallel edges included. A decomposition into
  cycles is a family `P` of cycles such that every edge lies in exactly one member of `P`.
-/

namespace OMA.S_opg_decomposing_an_eulerian_graph_into_cycles_with_no_two_consecutives_edges_on_a_pr

variable {V E : Type} [Fintype E] [DecidableEq V]

/-- Every vertex meets an even number of edges of `C`. -/
def IsEven (ends : E → Sym2 V) (C : Finset E) : Prop :=
  ∀ v : V, Even (C.filter fun e => v ∈ ends e).card

/-- A cycle: a minimal nonempty even edge set. -/
def IsCycle (ends : E → Sym2 V) (C : Finset E) : Prop :=
  C.Nonempty ∧ IsEven ends C ∧ ∀ C' ⊆ C, C'.Nonempty → IsEven ends C' → C' = C

theorem main :
    ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (ends : E → Sym2 V),
      (∀ e, ¬ (ends e).IsDiag) →
      (∀ v, 4 ≤ (Finset.univ.filter fun e => v ∈ ends e).card) →
      ∀ (m : ℕ) (τ : Fin m ≃ E) (w : Fin m → V),
        (∀ i, ends (τ i) = s(w i, w (finRotate m i))) →
        ∃ P : Finset (Finset E), (∀ C ∈ P, IsCycle ends C) ∧ (∀ e, ∃! C, C ∈ P ∧ e ∈ C) ∧
          ∀ C ∈ P, ∀ i, ¬ (τ i ∈ C ∧ τ (finRotate m i) ∈ C) := by
  sorry

end OMA.S_opg_decomposing_an_eulerian_graph_into_cycles_with_no_two_consecutives_edges_on_a_pr
