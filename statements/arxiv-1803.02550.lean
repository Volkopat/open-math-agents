import Mathlib

/-!
# Broadcast domination versus multipacking

Source: https://arxiv.org/abs/1803.02550 (Beaudou, Brewster, Foucaud, Broadcast domination and
multipacking: bounds and the integrality gap), Conjecture 2: for any graph G, γ_b(G) ≤ 2 mp(G).

A dominating broadcast is a function f : V → ℕ such that every vertex u has a vertex v with
f(v) > 0 and dist(u, v) ≤ f(v); its cost is ∑ f(v), and γ_b(G) is the minimum cost. A multipacking
is a set P of vertices such that for every vertex v and every positive integer r, the ball of
radius r around v contains at most r vertices of P; mp(G) is the maximum size of a multipacking.
Both parameters are additive over connected components (balls do not leave a component), so the
statement is stated for connected finite graphs on Fin n, where the graph distance is finite;
this is equivalent to the statement for all finite graphs.

Literature: the paper proves γ_b(G) ≤ 2 mp(G) + 3 and the conjecture when mp(G) ≤ 4; later work
(e.g. arXiv:2507.01565 on hypercubes) treats special classes only.
-/

namespace OMA.S_arxiv_1803_02550

/-- `f` is a dominating broadcast: every vertex is within distance `f v` of some `v` with
`f v > 0`. -/
def IsDominatingBroadcast {n : ℕ} (G : SimpleGraph (Fin n)) (f : Fin n → ℕ) : Prop :=
  ∀ u, ∃ v, 0 < f v ∧ G.dist u v ≤ f v

/-- The broadcast number `γ_b(G)`: the minimum cost of a dominating broadcast. -/
noncomputable def broadcastNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {c | ∃ f, IsDominatingBroadcast G f ∧ ∑ v, f v = c}

/-- `P` is a multipacking: every ball of radius `r ≥ 1` contains at most `r` vertices of `P`. -/
def IsMultipacking {n : ℕ} (G : SimpleGraph (Fin n)) (P : Finset (Fin n)) : Prop :=
  ∀ v, ∀ r ≥ 1, (P.filter fun u => G.dist v u ≤ r).card ≤ r

/-- The multipacking number `mp(G)`: the maximum size of a multipacking. -/
noncomputable def multipackingNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sSup {k | ∃ P, IsMultipacking G P ∧ P.card = k}

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected →
    broadcastNumber G ≤ 2 * multipackingNumber G := by
  sorry

end OMA.S_arxiv_1803_02550
