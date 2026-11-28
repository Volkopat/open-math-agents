import Mathlib

/-!
# Woodall's conjecture

Source: https://en.wikipedia.org/wiki/Woodall's_conjecture
Credit: @mattdorman

The source states Woodall's conjecture: the minimum number of edges in a dicut of a directed graph
is equal to the maximum number of disjoint dijoins.

Reading used here: the directed graph is a finite set `E` of arcs on a finite vertex type `V`.
A dicut is given by a vertex set `S`, neither empty nor everything, such that no arc enters `S`
from outside; its edges are the arcs leaving `S`. A dijoin is a set of arcs meeting every dicut.
One inequality is immediate (disjoint dijoins each use an arc of every dicut), so the conjecture
is the other one: if every dicut has at least `k` edges, there are `k` pairwise disjoint dijoins.
The statement is written in that form, which together with the immediate inequality is the
equality of the source.
-/

namespace OMA.S_wp_woodall_s_conjecture

/-- `S` determines a dicut: a proper nonempty vertex set that no arc enters. -/
def IsDicutSet {V : Type} [Fintype V] (E : Finset (V × V)) (S : Finset V) : Prop :=
  S.Nonempty ∧ S ≠ Finset.univ ∧ ∀ a ∈ E, a.1 ∉ S → a.2 ∉ S

/-- The edges of the dicut determined by `S`: the arcs leaving `S`. -/
def dicutEdges {V : Type} [DecidableEq V] (E : Finset (V × V)) (S : Finset V) : Finset (V × V) :=
  E.filter fun a => a.1 ∈ S ∧ a.2 ∉ S

/-- `J` is a dijoin: a set of arcs meeting every dicut. -/
def IsDijoin {V : Type} [Fintype V] [DecidableEq V] (E J : Finset (V × V)) : Prop :=
  J ⊆ E ∧ ∀ S : Finset V, IsDicutSet E S → (J ∩ dicutEdges E S).Nonempty

theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (E : Finset (V × V)) (k : ℕ),
      (∀ S : Finset V, IsDicutSet E S → k ≤ (dicutEdges E S).card) →
        ∃ J : Fin k → Finset (V × V), (∀ i, IsDijoin E (J i)) ∧
          ∀ i j, i ≠ j → Disjoint (J i) (J j) := by
  sorry

end OMA.S_wp_woodall_s_conjecture
