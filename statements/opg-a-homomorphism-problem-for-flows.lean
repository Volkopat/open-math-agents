import Mathlib

/-!
# A homomorphism problem for flows

Source: https://www.openproblemgarden.org/op/a_homomorphism_problem_for_flows
Credit: @shc261392

Conjecture (DeVos): let `M, M'` be abelian groups and let `B ⊆ M`, `B' ⊆ M'` satisfy `B = -B`
and `B' = -B'`. If there is a homomorphism from `Cayley(M, B)` to `Cayley(M', B')`, then every
graph with a `B`-flow has a `B'`-flow.

Reading used here:
* `Cayley(M, B)` has vertex set `M`, with `x` adjacent to `y` when `y - x ∈ B`. Here `0 ∉ B`
  and `0 ∉ B'` are assumed, so that these Cayley graphs are loopless and can be taken as simple
  graphs. (If `0 ∈ B` the `B`-flow condition is satisfied by the zero flow, and a homomorphism
  must send the loops at each vertex to loops, forcing `0 ∈ B'`; this degenerate case is
  dropped.)
* A graph is a finite multigraph, possibly with loops and parallel edges, given with a fixed
  orientation: a finite vertex type `V`, a finite edge type `E` and maps `src tgt : E → V`.
  Since `B = -B`, whether a `B`-flow exists does not depend on the orientation.
* A `B`-flow is a map `φ : E → M` with values in `B` such that at every vertex the total value
  on the edges entering it equals the total value on the edges leaving it.
-/

namespace OMA.S_opg_a_homomorphism_problem_for_flows

/-- The Cayley graph `Cayley(M, B)`. -/
def cay {M : Type} [AddCommGroup M] (B : Set M) : SimpleGraph M :=
  SimpleGraph.fromRel fun x y => y - x ∈ B

/-- The oriented multigraph `(src, tgt)` has a `B`-flow. -/
def HasFlow {M V E : Type} [AddCommGroup M] [DecidableEq V] [Fintype E] (B : Set M) (src tgt : E → V) :
    Prop :=
  ∃ φ : E → M, (∀ e, φ e ∈ B) ∧
    ∀ v : V, ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), φ e =
      ∑ e ∈ Finset.univ.filter (fun e => src e = v), φ e

theorem main :
    ∀ (M M' : Type) [AddCommGroup M] [AddCommGroup M'] (B : Set M) (B' : Set M'),
      -B = B → -B' = B' → (0 : M) ∉ B → (0 : M') ∉ B' →
      Nonempty (cay B →g cay B') →
      ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (src tgt : E → V),
        HasFlow B src tgt → HasFlow B' src tgt := by
  sorry

end OMA.S_opg_a_homomorphism_problem_for_flows
