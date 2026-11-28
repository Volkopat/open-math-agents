import Mathlib

/-!
# Strong 5-cycle double cover conjecture

Source: https://www.openproblemgarden.org/op/strong_5_cycle_double_cover_conjecture
Credit: @shc261392

Conjecture: let `C` be a circuit in a bridgeless cubic graph `G`. Then there is a five cycle
double cover of `G` such that `C` is a subgraph of one of these five cycles. Here a cycle is a
2-regular subgraph of `G` (possibly disconnected), and a five cycle double cover of `G` is a set
of five cycles of `G` such that every edge of `G` is contained in exactly two of them.

Reading used here:
* `G` is a finite loopless multigraph (`ends : E → Sym2 V`, no loops) in which every vertex
  meets exactly three edges.
* A cycle (2-regular subgraph) is identified with its edge set; in a cubic graph an edge set is
  the edge set of a 2-regular subgraph iff every vertex meets an even number (0 or 2) of its
  edges. The empty edge set is allowed (the empty 2-regular subgraph).
* A circuit is a connected 2-regular subgraph, i.e. a minimal nonempty even edge set.
* The five cycles are indexed by `Fin 5`.
* An edge `e` with ends `u, v` is a bridge if `u` and `v` are not joined by a path avoiding `e`.
-/

namespace OMA.S_opg_strong_5_cycle_double_cover_conjecture

variable {V E : Type} [Fintype E] [DecidableEq V]

/-- Every vertex meets an even number of edges of `C`. -/
def IsEven (ends : E → Sym2 V) (C : Finset E) : Prop :=
  ∀ v : V, Even (C.filter fun e => v ∈ ends e).card

/-- A circuit: a minimal nonempty even edge set. -/
def IsCircuit (ends : E → Sym2 V) (C : Finset E) : Prop :=
  C.Nonempty ∧ IsEven ends C ∧ ∀ C' ⊆ C, C'.Nonempty → IsEven ends C' → C' = C

/-- No edge is a bridge. -/
def Bridgeless (ends : E → Sym2 V) : Prop :=
  ∀ e u v, ends e = s(u, v) →
    Relation.ReflTransGen (fun a b => ∃ e', e' ≠ e ∧ ends e' = s(a, b)) u v

theorem main :
    ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (ends : E → Sym2 V),
      (∀ e, ¬ (ends e).IsDiag) →
      (∀ v, (Finset.univ.filter fun e => v ∈ ends e).card = 3) → Bridgeless ends →
      ∀ C : Finset E, IsCircuit ends C →
        ∃ D : Fin 5 → Finset E, (∀ i, IsEven ends (D i)) ∧
          (∀ e, (Finset.univ.filter fun i => e ∈ D i).card = 2) ∧ ∃ i, C ⊆ D i := by
  sorry

end OMA.S_opg_strong_5_cycle_double_cover_conjecture
