import Mathlib

/-!
# Kozma–Nitzan's post-FKG inequality for percolation on finite graphs

Source: https://arxiv.org/abs/2401.12397
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

G. Kozma and S. Nitzan, "A reduction of the `θ(p_c) = 0` problem to a conjectured inequality"
(arXiv:2401.12397). Setting: a finite graph `G` with an arbitrary probability `p(e)` on each edge,
edges open independently; `x ↔ y` means `x` and `y` are joined by an open path, and `0 ↔ A` means
`0` is joined to some vertex of `A`. Conjecture 1 (post-FKG):
  `P(0 ↔ b) ≥ P(0 ↔ A) · min { P(a ↔ b) : a ∈ A }`.
"We were not able to prove or disprove this conjecture." (The paper proves it for `|A| = 2` and in
some other special cases, and shows that a weakening of it implies `θ(p_c) = 0` on `ℤ^d`.) This file
states Conjecture 1.

Modelling choices:
* `G` is a finite simple graph on a finite vertex type `V`; `p : Sym2 V → ℝ` with values in
  `[0, 1]` gives the edge probabilities. The open-edge set `S ⊆ E(G)` has probability
  `∏_{e ∈ S} p(e) ∏_{e ∈ E(G) \ S} (1 - p(e))`, and the probability of an event is the sum of these
  weights over the configurations where it holds.
* `x ↔ y` in the configuration `S` is reachability in the graph with edge set `S`.
* `A` is a nonempty set of vertices (so that the minimum is defined); `0` and `b` are arbitrary
  vertices.
-/

namespace OMA.S_arxiv_2401_12397

open Classical

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Probability, under independent edge percolation on `G` with edge probabilities `p`, of the
event `E` (a property of the set of open edges). -/
noncomputable def prob (G : SimpleGraph V) [DecidableRel G.Adj] (p : Sym2 V → ℝ)
    (E : Finset (Sym2 V) → Prop) : ℝ :=
  ∑ S ∈ G.edgeFinset.powerset,
    (∏ e ∈ S, p e) * (∏ e ∈ G.edgeFinset \ S, (1 - p e)) * (if E S then 1 else 0)

/-- `x ↔ y` when the open edges are `S`. -/
def Conn (S : Finset (Sym2 V)) (x y : V) : Prop :=
  (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).Reachable x y

/-- **Kozma–Nitzan, Conjecture 1 (post-FKG inequality).** -/
theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (p : Sym2 V → ℝ), (∀ e, 0 ≤ p e ∧ p e ≤ 1) →
      ∀ (o b : V) (A : Finset V) (hA : A.Nonempty),
        prob G p (fun S => ∃ a ∈ A, Conn S o a) *
            A.inf' hA (fun a => prob G p (fun S => Conn S a b)) ≤
          prob G p (fun S => Conn S o b) := by
  sorry

end OMA.S_arxiv_2401_12397
