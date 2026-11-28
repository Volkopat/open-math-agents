import Mathlib

/-!
# Algorithm for graph homomorphisms

Source: https://www.openproblemgarden.org/op/algorithm_for_graph_homomorphisms
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Fomin, Heggernes, Kratsch): is there an algorithm that decides, for input graphs `G` and
`H`, whether there is a homomorphism from `G` to `H` in time `O(c^(|V(G)| + |V(H)|))` for some
constant `c`? `main` states the positive answer; a proof of its negation answers no.

Conventions:
* An instance is a pair of finite simple graphs on `Fin n` and `Fin m`, encoded over `Bool` as
  `1^n 0 1^m 0` followed by the adjacency bits of `G` (all ordered pairs, row by row) and then those
  of `H`.
* Algorithms are Mathlib's multi-stack Turing machines (`Turing.TM2ComputableInTime`), with the
  one-bit answer as output. Their time bound is a function of the input length; it is required to
  be at most `C * c ^ (n + m)` on every instance.
-/

namespace OMA.S_opg_algorithm_for_graph_homomorphisms

open Classical

/-- An instance: graphs `G` on `Fin n` and `H` on `Fin m`. -/
abbrev Inst : Type := Σ n m : ℕ, SimpleGraph (Fin n) × SimpleGraph (Fin m)

/-- Adjacency bits of a graph on `Fin n`, row by row. -/
noncomputable def adjBits {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool :=
  (List.finRange n).flatMap fun i => (List.finRange n).map fun j => decide (G.Adj i j)

/-- The binary encoding of an instance. -/
noncomputable def encode (x : Inst) : List Bool :=
  List.replicate x.1 true ++ [false] ++ List.replicate x.2.1 true ++ [false] ++
    adjBits x.2.2.1 ++ adjBits x.2.2.2

/-- The answer: is there a homomorphism `G →g H`? -/
noncomputable def hom (x : Inst) : Bool :=
  decide (Nonempty (x.2.2.1 →g x.2.2.2))

theorem main :
    ∃ C c : ℕ, ∃ M : Turing.TM2ComputableInTime encode (fun b : Bool => [b]) hom,
      ∀ x : Inst, M.time (encode x).length ≤ C * c ^ (x.1 + x.2.1) := by
  sorry

end OMA.S_opg_algorithm_for_graph_homomorphisms
