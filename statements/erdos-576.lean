import Mathlib

/-!
# Erdős Problem 576

Source: https://www.erdosproblems.com/576
Credit: @mgv27

Let $Q_k$ be the $k$-dimensional hypercube graph (so that $Q_k$ has $2^k$ vertices and
$k2^{k-1}$ edges). Determine the behaviour of
\[\mathrm{ex}(n;Q_k).\]

Formalization notes:
* "Determine the behaviour" is not a precise question. `main` states the specific question
  Erdős asked in [Er74c], [Er81], [Er93] (quoted on the source page): is
  $\mathrm{ex}(n;Q_3)\asymp n^{8/5}$?
* `Q₃` is the graph on `Fin 3 → Bool` where two vertices are adjacent iff they differ in exactly
  one coordinate. A quick check confirms it has `8` vertices and `12 = 3 · 2²` edges.
* `G` contains a copy of `Q₃` if there is an injective map from the vertices of `Q₃` into those
  of `G` sending edges to edges (a not necessarily induced subgraph).
* `ex(n; Q₃)` is the maximum number of edges of a simple graph on `Fin n` containing no copy of
  `Q₃` (the set of such values is nonempty, via the empty graph, and bounded by `n²`).
* `≍` is spelled out as: there are constants `c > 0`, `C > 0` and `N₀` with
  `c n^{8/5} ≤ ex(n; Q₃) ≤ C n^{8/5}` for all `n ≥ N₀`.
* The upper bound `ex(n; Q₃) ≪ n^{8/5}` is due to Erdős and Simonovits [ErSi70], who also
  proved `ex(n; Q₃) ≥ (1/2 + o(1)) n^{3/2}`; the open part is the matching lower bound.
-/

namespace OMA.S_erdos_576

open Filter

/-- The 3-dimensional hypercube graph `Q₃`: vertices `Fin 3 → Bool`, adjacent iff they differ in
exactly one coordinate. -/
def Q3 : SimpleGraph (Fin 3 → Bool) :=
  SimpleGraph.fromRel fun x y => (Finset.univ.filter fun i => x i ≠ y i).card = 1

/-- `G` contains a (not necessarily induced) copy of `Q₃`. -/
def ContainsQ3 {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ f : (Fin 3 → Bool) → V, Function.Injective f ∧ ∀ x y, Q3.Adj x y → G.Adj (f x) (f y)

/-- `ex(n; Q₃)`: the maximum number of edges of a graph on `n` vertices with no copy of `Q₃`. -/
noncomputable def ex (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ G : SimpleGraph (Fin n), ¬ ContainsQ3 G ∧ Nat.card G.edgeSet = k}

/-- Erdős Problem 576: is `ex(n; Q₃) ≍ n^{8/5}`? -/
theorem main : ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    c * (n : ℝ) ^ ((8 : ℝ) / 5) ≤ (ex n : ℝ) ∧ (ex n : ℝ) ≤ C * (n : ℝ) ^ ((8 : ℝ) / 5) := by
  sorry

end OMA.S_erdos_576
