import Mathlib

/-!
# Is `P_p(0 ↔ (0, n))` monotone in `n` for Bernoulli bond percolation on `ℤ²`?

Source: https://arxiv.org/abs/2601.00291
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

A. M. Campos and B. N. B. de Lima, "The probability of connection between two vertices cannot be
monotone with the distance for Bernoulli Percolation on transitive graphs" (arXiv:2601.00291). The
abstract states: "on the square lattice is an open question to prove that the probability of the
origin being connected to the vertex `(0, n)` is monotone in `n`". In the paper, a graph has the
monotonic property at `p` if `P_p(o ↔ x) ≥ P_p(o ↔ y)` whenever `‖x‖ < ‖y‖` (graph distance), and
whether `ℤ^d` has it is open for all `d ≥ 2`; the paper constructs other transitive graphs without
it. This file states the square-lattice question from the abstract, for every `p ∈ [0, 1]`:
`n ↦ P_p(0 ↔ (0, n))` is nonincreasing.

Modelling choices:
* Bernoulli bond percolation on `ℤ²` with parameter `p`: each nearest-neighbour edge is open
  independently with probability `p`. The edge from `z` to `z + (1, 0)` is indexed by `(z, 0)` and
  the edge from `z` to `z + (0, 1)` by `(z, 1)`; the states are measurable, mutually independent
  (`iIndepFun`) `Bool`-valued variables with `P[open] = p` on an arbitrary probability space.
* `0 ↔ x` means `x` is reached from the origin by a finite path of open edges (the
  reflexive–transitive closure of "joined by an open edge").
-/

namespace OMA.S_arxiv_2601_00291

open MeasureTheory ProbabilityTheory

/-- The unit vector of direction `k` (`0`: horizontal, `1`: vertical). -/
def e (k : Fin 2) : ℤ × ℤ := if k = 0 then (1, 0) else (0, 1)

/-- `z` and `w` are joined by an edge that is open in the configuration `ω`. -/
def openEdge (ω : (ℤ × ℤ) × Fin 2 → Bool) (z w : ℤ × ℤ) : Prop :=
  ∃ k : Fin 2, (w = z + e k ∧ ω (z, k) = true) ∨ (z = w + e k ∧ ω (w, k) = true)

/-- The origin is connected to `x` by a path of open edges. -/
def Connected (ω : (ℤ × ℤ) × Fin 2 → Bool) (x : ℤ × ℤ) : Prop :=
  Relation.ReflTransGen (openEdge ω) (0, 0) x

/-- **Monotonicity of the two-point function along an axis in `ℤ²` (open question).** -/
theorem main :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (p : ℝ) (C : (ℤ × ℤ) × Fin 2 → Ω → Bool),
      0 ≤ p → p ≤ 1 →
      (∀ i, Measurable (C i)) →
      iIndepFun C μ →
      (∀ i, μ {ω | C i ω = true} = ENNReal.ofReal p) →
      ∀ n : ℕ,
        μ {ω | Connected (fun i => C i ω) (0, (n : ℤ) + 1)} ≤
          μ {ω | Connected (fun i => C i ω) (0, (n : ℤ))} := by
  sorry

end OMA.S_arxiv_2601_00291
