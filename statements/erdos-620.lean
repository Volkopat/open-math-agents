import Mathlib

/-!
# Erdős Problem 620 (the Erdős–Rogers problem)

Source: https://www.erdosproblems.com/620
Credit: @jbhooper9000

## The problem (as stated at the source, [ErRo62][EGT92][Er99])

If $G$ is a graph on $n$ vertices without a $K_4$ then how large a triangle-free induced
subgraph must $G$ contain?

The source lets $f(n)$ be such that every such graph contains a triangle-free subgraph with at
least $f(n)$ vertices. Known: $f(n) = n^{1/2+o(1)}$; Bollobás–Hind, Krivelevich, Wolfovitz;
the bounds $n^{1/2}(\log n)^{1/2}/\log\log n \ll f(n) \ll n^{1/2}\log n$ (Shearer; Mubayi and
Verstraete [MuVe24]). On the source forum (2026-09-07) it is reported that Morris,
Sahasrabudhe and Verstraete (arXiv:2607.16118) determined the order of growth:
$f(n) = \Theta(\sqrt{n \log n})$.

## Formalization notes

* Graphs on `n` vertices are `SimpleGraph (Fin n)`; "without a `K₄`" is `G.CliqueFree 4`.
* A triangle-free induced subgraph is determined by its vertex set `s`: it is triangle-free
  iff no 3-element subset of `s` is a triangle of `G` (`IsTriangleFreeSet G s`).
* `f n` is the largest `m` such that every `K₄`-free graph on `n` vertices has a triangle-free
  induced subgraph on `m` vertices (the source's `f(n)`, taken optimal). The set of such `m`
  contains `0` and is bounded by `n`, so `sSup` is its maximum.
* "How large must it be?" is answered by stating the order of growth reported on the source
  forum, `f(n) = Θ(√(n log n))`, as an `Asymptotics.IsTheta` statement (constants are not
  specified, matching `Θ`).
-/

namespace OMA.S_erdos_620

open Filter Asymptotics

/-- `s` spans a triangle-free induced subgraph of `G`: no three vertices of `s` form a
triangle in `G`. -/
def IsTriangleFreeSet {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) : Prop :=
  ∀ t ⊆ s, ¬ G.IsNClique 3 t

/-- `f n`: the largest `m` such that every `K₄`-free graph on `n` vertices contains a
triangle-free induced subgraph on `m` vertices. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
    ∃ s : Finset (Fin n), s.card = m ∧ IsTriangleFreeSet G s}

/-- Erdős Problem 620 (Erdős–Rogers), with the order of growth reported on the source:
`f(n) = Θ(√(n log n))`. -/
theorem main :
    (fun n : ℕ => (f n : ℝ)) =Θ[atTop] (fun n : ℕ => Real.sqrt ((n : ℝ) * Real.log n)) := by
  sorry

end OMA.S_erdos_620
