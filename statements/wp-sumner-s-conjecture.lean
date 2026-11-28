import Mathlib

/-!
# Sumner's conjecture (Sumner's universal tournament conjecture)

Source: https://en.wikipedia.org/wiki/Sumner's_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source statement (Sumner, 1971): every orientation of every `n`-vertex tree is a subgraph of
every `(2n - 2)`-vertex tournament. Equivalently (the source's unsolved-problem box): does every
`(2n - 2)`-vertex tournament contain as a subgraph every `n`-vertex oriented tree?

Conventions:
* `n ≥ 2`. For `n = 1` the tournament would have `0` vertices and could not contain the
  one-vertex tree, so the statement is only meaningful from `n = 2` on (the literature, e.g.
  Kühn–Mycroft–Osthus, states it for `n ≥ 2`); `n = 0` is degenerate;
* a tournament on the vertex set `Fin (2 * n - 2)` is a relation `T` (`T x y` means the arc goes
  from `x` to `y`) such that for all `x ≠ y` exactly one of `T x y`, `T y x` holds, and `T x x`
  never holds;
* an oriented tree on `Fin n` is a relation `O` with no loops and no pair of opposite arcs,
  whose underlying undirected simple graph (`SimpleGraph.fromRel O`) is a tree (Mathlib's
  `SimpleGraph.IsTree`). Every orientation of every `n`-vertex tree arises this way up to
  relabelling the vertices;
* `O` is a subgraph of `T` when there is an injective map `f : Fin n → Fin (2 * n - 2)` sending
  every arc of `O` to an arc of `T` with the same direction. Non-arcs need not be preserved
  (a tournament has an arc between every pair, so the copy is a subgraph, not an induced one).
-/

namespace OMA.S_wp_sumner_s_conjecture

/-- `T` is a tournament on `V`: loopless, and exactly one direction between distinct vertices. -/
def IsTournament {V : Type} (T : V → V → Prop) : Prop :=
  (∀ x, ¬ T x x) ∧ (∀ x y, x ≠ y → (T x y ∨ T y x)) ∧ (∀ x y, T x y → ¬ T y x)

/-- `O` is an oriented tree on `V`: no loops, no opposite arcs, and the underlying undirected
graph is a tree. -/
def IsOrientedTree {V : Type} (O : V → V → Prop) : Prop :=
  (∀ x, ¬ O x x) ∧ (∀ x y, O x y → ¬ O y x) ∧ (SimpleGraph.fromRel O).IsTree

theorem main : ∀ n : ℕ, 2 ≤ n →
    ∀ (T : Fin (2 * n - 2) → Fin (2 * n - 2) → Prop), IsTournament T →
    ∀ (O : Fin n → Fin n → Prop), IsOrientedTree O →
    ∃ f : Fin n → Fin (2 * n - 2), Function.Injective f ∧ ∀ x y, O x y → T (f x) (f y) := by
  sorry

end OMA.S_wp_sumner_s_conjecture
