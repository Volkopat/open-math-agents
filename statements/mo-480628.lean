import Mathlib

/-!
# Removing edges on the left does not make exiting to the left more likely

Source: https://mathoverflow.net/questions/480628
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 480628, Frederik Ravn Klausen, Oct 2024): let `G = (V, E)` with
`V = {1, …, 2N+1} × {1, …, 2N+1}` and an edge between `(n, m)` and `(n', m')` iff
`|n - n'| + |m - m'| = 1`. Remove some arbitrary edges between vertices `(n, m)` and `(n', m')` with
`n, n' ≤ N` (before sampling). On the remaining graph consider Bernoulli edge percolation with
parameter `p ∈ [0, 1]` (each remaining edge is kept with probability `p`). Prove or disprove that, no
matter which edges were deleted, the probability that there is a path from `(N+1, N+1)` to a vertex
`(2N+1, m)` is at least the probability that there is a path to a vertex `(1, m)`. (The page links a
counterexample to a related statement about numbers of paths.) The page has no answer; `main` states
the affirmative answer.

Modelling choices:
* Coordinates are `0`-indexed: `V = Fin (2N+1) × Fin (2N+1)`, the centre is `(N, N)`, the left and
  right columns are first coordinate `0` and `2N`, and "both endpoints have `n, n' ≤ N`" (`1`-indexed)
  becomes first coordinates `< N`.
* The removed set `R` is any set of edges all of whose endpoints have first coordinate `< N`; the
  remaining graph is `grid.deleteEdges R`. Percolation probabilities are finite sums over the sets
  `S` of open edges of the remaining graph, with weight `p^{|S|} (1-p)^{|E| - |S|}`; a path exists
  iff the endpoints are reachable in the graph with edge set `S`.
-/

namespace OMA.S_mo_480628

open Classical

/-- The vertex set `{0, …, 2N} × {0, …, 2N}`. -/
abbrev V (N : ℕ) := Fin (2 * N + 1) × Fin (2 * N + 1)

/-- The grid graph: `u ~ v` iff they differ by `1` in exactly one coordinate. -/
def grid (N : ℕ) : SimpleGraph (V N) :=
  SimpleGraph.fromRel fun u v =>
    ((u.1 : ℕ) + 1 = v.1 ∧ u.2 = v.2) ∨ (u.1 = v.1 ∧ (u.2 : ℕ) + 1 = v.2)

/-- The probability, under Bernoulli(`p`) percolation on `H`, of the event `E`. -/
noncomputable def prob {N : ℕ} (H : SimpleGraph (V N)) (p : ℝ) (E : Finset (Sym2 (V N)) → Prop) :
    ℝ :=
  ∑ S ∈ H.edgeFinset.powerset,
    p ^ S.card * (1 - p) ^ (H.edgeFinset.card - S.card) * (if E S then 1 else 0)

/-- With open edges `S`, the centre `(N, N)` is joined to some vertex of column `col`. -/
def ReachesColumn {N : ℕ} (S : Finset (Sym2 (V N))) (col : Fin (2 * N + 1)) : Prop :=
  ∃ m : Fin (2 * N + 1),
    (SimpleGraph.fromEdgeSet (S : Set (Sym2 (V N)))).Reachable
      (⟨N, by omega⟩, ⟨N, by omega⟩) (col, m)

/-- **MathOverflow 480628 (affirmative answer).** -/
theorem main :
    ∀ (N : ℕ) (R : Set (Sym2 (V N))), (∀ e ∈ R, ∀ v ∈ e, (v.1 : ℕ) < N) →
      ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
        prob ((grid N).deleteEdges R) p (fun S => ReachesColumn S ⟨0, by omega⟩) ≤
          prob ((grid N).deleteEdges R) p (fun S => ReachesColumn S ⟨2 * N, by omega⟩) := by
  sorry

end OMA.S_mo_480628
