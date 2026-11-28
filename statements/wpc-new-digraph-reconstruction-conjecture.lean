import Mathlib

/-!
# New digraph reconstruction conjecture

Source: https://en.wikipedia.org/wiki/New_digraph_reconstruction_conjecture
Credit: @pyaf (agent: Claude Code, model claude-opus-5-5)

Source statement (Ramachandran, 1979; J. Combin. Theory Ser. B 31 (1981) 143–149):
"If `D` and `E` are any two digraphs and `ƒ` is a bijection from `V(D)` to `V(E)` such that
`D \ {v}` and `E \ {ƒ(v)}` are isomorphic and `(od(v), id(v)) = (od(ƒ(v)), id(ƒ(v)))` for all `v`
in `V(D)`, then `D` and `E` are isomorphic."
Here `od(v)` (resp. `id(v)`) is the number of arcs from (resp. to) `v`.

Conventions:
* digraphs are in Harary's sense (the source uses Harary's terminology): a finite vertex set and
  a set of ordered pairs of distinct vertices, i.e. a Mathlib `Digraph` on a `Fintype` with no
  loops; there are no multiple arcs, while opposite arcs `u → w`, `w → u` may both occur;
* `D \ {v}` is the subdigraph induced on the remaining vertices;
* an isomorphism of digraphs is a bijection of vertices preserving and reflecting arcs, i.e. a
  `RelIso` between the adjacency relations;
* the source puts no lower bound on the number of vertices (on at most two vertices the statement
  holds trivially).
-/

namespace OMA.S_wpc_new_digraph_reconstruction_conjecture

open Classical

/-- The out-degree `od(v)`: the number of arcs from `v`. -/
noncomputable def outDeg {V : Type} [Fintype V] (D : Digraph V) (v : V) : ℕ :=
  (Finset.univ.filter (fun w => D.Adj v w)).card

/-- The in-degree `id(v)`: the number of arcs to `v`. -/
noncomputable def inDeg {V : Type} [Fintype V] (D : Digraph V) (v : V) : ℕ :=
  (Finset.univ.filter (fun w => D.Adj w v)).card

/-- The vertex-deleted subdigraphs `D \ {v}` and `E \ {w}` are isomorphic. -/
def CardsIso {V W : Type} (D : Digraph V) (E : Digraph W) (v : V) (w : W) : Prop :=
  Nonempty ((fun a b : {x : V // x ≠ v} => D.Adj a b) ≃r (fun a b : {y : W // y ≠ w} => E.Adj a b))

/-- The new digraph reconstruction conjecture. -/
theorem main : ∀ (V W : Type) [Fintype V] [Fintype W] (D : Digraph V) (E : Digraph W),
    (∀ v, ¬ D.Adj v v) → (∀ w, ¬ E.Adj w w) →
    ∀ f : V ≃ W, (∀ v, CardsIso D E v (f v) ∧
      outDeg D v = outDeg E (f v) ∧ inDeg D v = inDeg E (f v)) →
    Nonempty (D.Adj ≃r E.Adj) := by
  sorry

end OMA.S_wpc_new_digraph_reconstruction_conjecture
