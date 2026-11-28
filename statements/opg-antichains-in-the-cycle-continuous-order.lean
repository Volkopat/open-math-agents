import Mathlib

/-!
# Antichains in the cycle continuous order

Source: https://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order
Credit: @lzvxck

The source: if `G, H` are graphs, a function `f : E(G) → E(H)` is called cycle-continuous if
the pre-image of every element of the (binary) cycle space of `H` is a member of the cycle
space of `G`. Problem: does there exist an infinite set of graphs `{G_1, G_2, ...}` so that
there is no cycle continuous mapping between `G_i` and `G_j` whenever `i ≠ j`? (The order is
taken on finite graphs with at least one edge.)

The existence (affirmative) form is stated. Conventions: graphs are finite multigraphs
(parallel edges and loops allowed; the page's examples use parallel edges), each with at least
one edge: a finite vertex type `V`, a finite edge type `E`, and two ends `src e`, `tgt e` for
each edge. The binary cycle space of a graph is the set of edge sets in which every vertex has
even degree (a loop counting twice). Since `i ≠ j` ranges over both orders, there is no
cycle-continuous map from `G_i` to `G_j` nor from `G_j` to `G_i`; the graphs are then
automatically pairwise distinct (the identity map is cycle-continuous), so the set is infinite.
-/

namespace OMA.S_opg_antichains_in_the_cycle_continuous_order

/-- `S` is in the binary cycle space of the multigraph `(V, E, src, tgt)`: every vertex has
even degree in `S`. -/
def IsInCycleSpace {V E : Type*} [DecidableEq V] (src tgt : E → V) (S : Finset E) : Prop :=
  ∀ v, Even ((S.filter fun e => src e = v).card + (S.filter fun e => tgt e = v).card)

/-- `f` is cycle-continuous from `(V, E, src, tgt)` to `(V', E', src', tgt')`: the preimage of
every element of the cycle space of the target is in the cycle space of the source. -/
def IsCycleContinuous {V E V' E' : Type*} [Fintype E] [DecidableEq V] [DecidableEq V']
    [DecidableEq E'] (src tgt : E → V) (src' tgt' : E' → V') (f : E → E') : Prop :=
  ∀ T : Finset E', IsInCycleSpace src' tgt' T →
    IsInCycleSpace src tgt (Finset.univ.filter fun e => f e ∈ T)

/-- **Antichains in the cycle-continuous order (DeVos).** There is a sequence of finite
multigraphs with at least one edge, with no cycle-continuous mapping between `G_i` and `G_j`
for `i ≠ j`. -/
theorem main : ∃ (V E : ℕ → Type) (_ : ∀ i, Fintype (V i)) (_ : ∀ i, DecidableEq (V i))
    (_ : ∀ i, Fintype (E i)) (_ : ∀ i, DecidableEq (E i)) (src tgt : ∀ i, E i → V i),
      (∀ i, Nonempty (E i)) ∧
        ∀ i j, i ≠ j → ∀ f : E i → E j, ¬ IsCycleContinuous (src i) (tgt i) (src j) (tgt j) f := by
  sorry

end OMA.S_opg_antichains_in_the_cycle_continuous_order
