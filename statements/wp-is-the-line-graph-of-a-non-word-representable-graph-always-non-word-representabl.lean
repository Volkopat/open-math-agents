import Mathlib

/-!
# Is the line graph of a non-word-representable graph always non-word-representable?

Source: https://en.wikipedia.org/wiki/Word-representable_graph#Open_problems
(catalogue link: https://en.wikipedia.org/wiki/line_graph)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source definitions: a graph `G` with vertex set `V` is word-representable if there is a word `w`
over the alphabet `V` such that letters `a` and `b` alternate in `w` if and only if `ab` is an
edge of `G`; `a` and `b` alternate in `w` if, after removing from `w` all letters but the copies
of `a` and `b`, one obtains a word `abab...` or `baba...`. Open problem listed there: is the line
graph of a non-word-representable graph always non-word-representable? The affirmative answer
is stated.

Conventions:
* graphs are finite simple graphs; the line graph is Mathlib's `SimpleGraph.lineGraph`
  (vertices are the edges of `G`, adjacent when distinct and sharing an endpoint);
* a word is a `List V`, and, as in Kitaev's definition, a representing word contains every
  vertex (letter) at least once;
* `a` and `b` (distinct) alternate in `w` when the subword of `w` formed by the copies of `a` and
  `b` has no two equal consecutive letters (equivalently it is `abab...` or `baba...`); the
  condition is required only for distinct `a`, `b`, since simple graphs have no loops.
-/

namespace OMA.S_wp_is_the_line_graph_of_a_non_word_representable_graph_always_non_word_representabl

/-- Letters `a` and `b` alternate in the word `w`: deleting every other letter leaves a word with
no two equal consecutive letters. -/
def Alternate {V : Type} [DecidableEq V] (w : List V) (a b : V) : Prop :=
  List.IsChain (· ≠ ·) (w.filter fun z => decide (z = a ∨ z = b))

/-- `G` is word-representable: some word containing every vertex has `a`, `b` alternating exactly
when `a` and `b` are adjacent. -/
def IsWordRepresentable {V : Type} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ w : List V, (∀ v : V, v ∈ w) ∧ ∀ a b : V, a ≠ b → (G.Adj a b ↔ Alternate w a b)

theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ¬ IsWordRepresentable G → ¬ IsWordRepresentable G.lineGraph := by
  sorry

end OMA.S_wp_is_the_line_graph_of_a_non_word_representable_graph_always_non_word_representabl
