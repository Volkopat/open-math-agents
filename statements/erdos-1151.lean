import Mathlib

/-!
# Erdős Problem 1151

Source: https://www.erdosproblems.com/1151
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `𝓛ⁿf` be the Lagrange interpolation polynomial of `f` at the `n` Chebyshev nodes of
`[-1, 1]`. For any closed `A ⊆ [-1, 1]` there is a continuous `f` such that `A` is the set of
limit points of `𝓛ⁿf(x)`.

## Encoding

* The Chebyshev nodes of order `n` are `cos ((2i + 1)π / (2n))`, `i = 0, …, n - 1`;
  `𝓛ⁿf` is Mathlib's `Lagrange.interpolate` at these nodes (degree `< n`).
* The source leaves the point `x` unspecified. Following Erdős's claim recorded there [Er43],
  `x` is any point of the form `cos (π p / q)` with `p, q ≥ 1` odd, and the limit points are those
  of the real sequence `n ↦ 𝓛ⁿf(x)` (cluster points, `MapClusterPt`).
* `f` is a real function continuous on `[-1, 1]`; `A` is required nonempty (an empty set of real
  limit points would mean `|𝓛ⁿf(x)| → ∞`, a different phenomenon covered by [Er41]).
-/

namespace OMA.S_erdos_1151

open Polynomial Filter

/-- The `n` Chebyshev nodes `cos ((2i + 1)π / (2n))`. -/
noncomputable def chebNode (n : ℕ) (i : Fin n) : ℝ :=
  Real.cos ((2 * (i : ℝ) + 1) * Real.pi / (2 * n))

/-- `𝓛ⁿf`: the Lagrange interpolation polynomial of `f` at the Chebyshev nodes of order `n`. -/
noncomputable def chebInterp (f : ℝ → ℝ) (n : ℕ) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (chebNode n) (fun i => f (chebNode n i))

theorem main :
    ∀ p q : ℕ, Odd p → Odd q →
      ∀ A : Set ℝ, IsClosed A → A.Nonempty → A ⊆ Set.Icc (-1) 1 →
        ∃ f : ℝ → ℝ, ContinuousOn f (Set.Icc (-1) 1) ∧
          {y : ℝ | MapClusterPt y atTop
            (fun n : ℕ => (chebInterp f n).eval (Real.cos (Real.pi * p / q)))} = A := by
  sorry

end OMA.S_erdos_1151
