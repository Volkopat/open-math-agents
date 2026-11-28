import Mathlib

/-!
# Faithful cycle covers

Source: https://www.openproblemgarden.org/op/faithful_cycle_covers
Credit: @shc261392

Conjecture (DeVos): if `G = (V, E)` is a graph, `p : E → ℤ` is admissible, and `p(e)` is even
for every `e ∈ E`, then `(G, p)` has a faithful cover.

Definitions from the source: a list `L` of cycles of `G` is a faithful (cycle) cover of `(G, p)`
if every edge `e` occurs in exactly `p(e)` cycles of `L`. The map `p` is admissible if
(i) `p` is nonnegative, (ii) `p(S)` is even for every edge-cut `S`, and (iii) `p(e) ≤ p(S)/2`
for every edge-cut `S` and edge `e ∈ S`. (With `p = 2` this is the cycle double cover
conjecture for bridgeless graphs.)

Reading used here:
* `G` is a finite loopless multigraph: a finite vertex type `V`, a finite edge type `E` and
  `ends : E → Sym2 V` with no loops.
* The edge-cut of `X ⊆ V` is the set of edges with exactly one end in `X`; `p(S)` is the sum of
  `p` over `S`.
* An edge set is even when every vertex meets an even number of its edges. A cycle is (the edge
  set of) a minimal nonempty even edge set; in a loopless multigraph these are exactly the edge
  sets of cycles (connected 2-regular subgraphs, including 2-cycles formed by parallel edges).
* The list `L` is a multiset of cycles.
-/

namespace OMA.S_opg_faithful_cycle_covers

variable {V E : Type} [Fintype E] [DecidableEq V]

/-- The edge-cut of a vertex set `X`: edges with exactly one end in `X`. -/
noncomputable def cut (ends : E → Sym2 V) (X : Set V) : Finset E := by
  classical
  exact Finset.univ.filter fun e => ∃ x ∈ X, ∃ y ∉ X, ends e = s(x, y)

/-- Every vertex meets an even number of edges of `C`. -/
def IsEven (ends : E → Sym2 V) (C : Finset E) : Prop :=
  ∀ v : V, Even (C.filter fun e => v ∈ ends e).card

/-- `C` is (the edge set of) a cycle: a minimal nonempty even edge set. -/
def IsCycle (ends : E → Sym2 V) (C : Finset E) : Prop :=
  C.Nonempty ∧ IsEven ends C ∧ ∀ C' ⊆ C, C'.Nonempty → IsEven ends C' → C' = C

/-- `p` is admissible. -/
def Admissible (ends : E → Sym2 V) (p : E → ℤ) : Prop :=
  (∀ e, 0 ≤ p e) ∧ (∀ X : Set V, Even (∑ e ∈ cut ends X, p e)) ∧
    ∀ X : Set V, ∀ e ∈ cut ends X, 2 * p e ≤ ∑ f ∈ cut ends X, p f

theorem main :
    ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (ends : E → Sym2 V),
      (∀ e, ¬ (ends e).IsDiag) → ∀ p : E → ℤ, Admissible ends p → (∀ e, Even (p e)) →
        ∃ L : Multiset (Finset E), (∀ C ∈ L, IsCycle ends C) ∧
          ∀ e, ((L.filter fun C => e ∈ C).card : ℤ) = p e := by
  sorry

end OMA.S_opg_faithful_cycle_covers
