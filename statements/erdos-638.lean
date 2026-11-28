import Mathlib

/-!
# Erdős Problem 638

Source: https://www.erdosproblems.com/638
Credit: @mgv27

Let $S$ be a family of finite graphs such that for every $n$ there is some $G_n\in S$ such that
if the edges of $G_n$ are coloured with $n$ colours then there is a monochromatic triangle. Is it
true that for every infinite cardinal $\aleph$ there is a graph $G$ of which every finite subgraph
is in $S$ and if the edges of $G$ are coloured with $\aleph$ many colours then there is a
monochromatic triangle.

Formalization notes:
* A finite graph is a `SimpleGraph (Fin m)`; the family `S` is given by `S m`, the graphs in it
  on vertex set `Fin m`.
* Following Barreto's remark on the source page, `S` is assumed closed under taking (not
  necessarily induced) subgraphs, via `SubgraphClosed`; otherwise a sparse family of complete
  graphs is a trivial counterexample. Since relabellings are injective maps, this also makes `S`
  closed under isomorphism, so "is in `S`" needs no separate up-to-isomorphism clause.
* "Every finite subgraph of `G` is in `S`" is: for every injective `f : Fin k → V` and every
  graph `H` on `Fin k` whose edges map to edges of `G` under `f`, `H ∈ S k`.
* An edge colouring with colour set `α` is a map `c : Sym2 V → α` (only its values on edges of
  `G` matter). A monochromatic triangle is three pairwise adjacent vertices whose three edges get
  the same colour.
* "Coloured with `n` colours" uses the colour set `Fin n`; for `n = 0` the hypothesis is
  harmless (a graph with an edge has no such colouring, so the condition holds vacuously).
* "Coloured with `ℵ` many colours" for an infinite cardinal `ℵ` is any colour type `α : Type`
  with `ℵ₀ ≤ #α`; the vertex type of `G` is any `V : Type`.
-/

namespace OMA.S_erdos_638

open Cardinal

/-- Every edge colouring `c : Sym2 V → α` of `G` has a monochromatic triangle. -/
def ArrowsTriangle {V : Type} (G : SimpleGraph V) (α : Type) : Prop :=
  ∀ c : Sym2 V → α, ∃ a b d : V, G.Adj a b ∧ G.Adj b d ∧ G.Adj a d ∧
    c s(a, b) = c s(b, d) ∧ c s(a, b) = c s(a, d)

/-- The family `S` is closed under taking subgraphs: if `G ∈ S m` and `H` on `Fin k` maps
injectively into `G` sending edges to edges, then `H ∈ S k`. -/
def SubgraphClosed (S : ∀ m : ℕ, Set (SimpleGraph (Fin m))) : Prop :=
  ∀ (k m : ℕ) (G : SimpleGraph (Fin m)), G ∈ S m → ∀ (f : Fin k → Fin m), Function.Injective f →
    ∀ H : SimpleGraph (Fin k), (∀ a b, H.Adj a b → G.Adj (f a) (f b)) → H ∈ S k

/-- Every finite subgraph of `G` is in `S`. -/
def FiniteSubgraphsIn (S : ∀ m : ℕ, Set (SimpleGraph (Fin m))) {V : Type}
    (G : SimpleGraph V) : Prop :=
  ∀ (k : ℕ) (f : Fin k → V), Function.Injective f →
    ∀ H : SimpleGraph (Fin k), (∀ a b, H.Adj a b → G.Adj (f a) (f b)) → H ∈ S k

/-- Erdős Problem 638: if a subgraph-closed family `S` of finite graphs contains, for every `n`,
a graph with the triangle Ramsey property for `n` colours, then for every infinite cardinal there
is a graph all of whose finite subgraphs lie in `S` with the triangle Ramsey property for that
many colours. -/
theorem main : ∀ S : ∀ m : ℕ, Set (SimpleGraph (Fin m)), SubgraphClosed S →
    (∀ n : ℕ, ∃ m : ℕ, ∃ G ∈ S m, ArrowsTriangle G (Fin n)) →
    ∀ α : Type, ℵ₀ ≤ #α →
      ∃ (V : Type) (G : SimpleGraph V), FiniteSubgraphsIn S G ∧ ArrowsTriangle G α := by
  sorry

end OMA.S_erdos_638
