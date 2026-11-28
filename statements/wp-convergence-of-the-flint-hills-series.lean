import Mathlib

/-!
# Convergence of the Flint Hills series

Source: https://en.wikipedia.org/wiki/Flint_Hills_series
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: the **Flint Hills series** is the series of real numbers
`sum over n >= 1 of 1 / (n ^ 3 * sin (n) ^ 2)`, where `sin` is taken in radians.  Whether this
series converges is an open question; it is related to how well the convergents of `pi` approximate
`pi`.

So the proposition formalized below is: the sequence `n ↦ 1 / ((n + 1) ^ 3 * sin (n + 1) ^ 2)`,
which is the Flint Hills series with the index starting at `1`, is summable.
-/

namespace OMA.S_wp_convergence_of_the_flint_hills_series

-- definitions the statement needs (no sorry, no axiom)

/-- The **Flint Hills series**, indexed from `1`: the term at `n` is `1 / (m ^ 3 * sin m ^ 2)` for
`m = n + 1`. -/
noncomputable def flintHillsSeries (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) ^ 3 * (Real.sin ((n : ℝ) + 1)) ^ 2)

/-- Does the Flint Hills series converge? -/
theorem main : Summable flintHillsSeries := by
  sorry

end OMA.S_wp_convergence_of_the_flint_hills_series
