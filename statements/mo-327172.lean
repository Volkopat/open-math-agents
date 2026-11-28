import Mathlib

/-!
# The Cuckoo Cycle conjecture

Source: https://mathoverflow.net/questions/327172
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Take a random bipartite multigraph with `N` edges on two sides of `N` nodes each, the endpoints of
each edge independent and uniform. A trimming round removes every edge whose endpoint on one side
has degree `1` (among the remaining edges); rounds alternate between the two sides, starting with
the first. Conjecture (Tromp): the fraction `fᵢ` of edges remaining after `i` rounds tends, as
`N → ∞`, to `a_{i-1} aᵢ`, where `a₋₁ = a₀ = 1` and `a_{i+1} = 1 - e^(-aᵢ)`.

Conventions:
* A graph is `g : Fin N → Fin N × Fin N` (edge `e` joins `(g e).1` on side `0` to `(g e).2` on
  side `1`); all `N^(2N)` graphs are equally likely, and `fᵢ` is read as the expected fraction
  `E[#remaining edges]/N`.
* `seqA i` is `a_{i-1}` (so `seqA 0 = seqA 1 = 1`); `main` states the limit for every `i ≥ 0`
  (for `i = 0` both sides are `1`).
-/

namespace OMA.S_mo_327172

open Filter Topology

/-- The endpoint of edge `e` on side `s` (`s = 0` or `1`). -/
def endpt {N : ℕ} (g : Fin N → Fin N × Fin N) (s : Bool) (e : Fin N) : Fin N :=
  if s then (g e).2 else (g e).1

/-- One trimming round on side `s`: keep the edges whose side-`s` endpoint has degree `≥ 2`
among the edges of `E`. -/
def trim {N : ℕ} (g : Fin N → Fin N × Fin N) (s : Bool) (E : Finset (Fin N)) : Finset (Fin N) :=
  E.filter fun e => 2 ≤ (E.filter fun e' => endpt g s e' = endpt g s e).card

/-- The edges remaining after `i` rounds (round `j + 1` trims side `j mod 2`). -/
def remaining {N : ℕ} (g : Fin N → Fin N × Fin N) : ℕ → Finset (Fin N)
  | 0 => Finset.univ
  | i + 1 => trim g (decide (i % 2 = 1)) (remaining g i)

/-- Expected fraction of edges remaining after `i` rounds. -/
noncomputable def f (N i : ℕ) : ℝ :=
  (∑ g : Fin N → Fin N × Fin N, ((remaining g i).card : ℝ)) / ((N : ℝ) ^ (2 * N) * N)

/-- `seqA i = a_{i-1}`: `1, 1, 1 - e⁻¹, …`. -/
noncomputable def seqA : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | i + 2 => 1 - Real.exp (-seqA (i + 1))

/-- `fᵢ → a_{i-1} aᵢ` for every `i`. -/
theorem main : ∀ i : ℕ,
    Tendsto (fun N : ℕ => f N i) atTop (𝓝 (seqA i * seqA (i + 1))) := by
  sorry

end OMA.S_mo_327172
