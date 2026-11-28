import Mathlib

/-!
# A041243: Denominators of continued fraction convergents to sqrt(133).

Source: https://oeis.org/A041243
Credit: @physbuzz

Conjecture (Harvey P. Dale, Dec 03 2022): the sequence satisfies a linear recurrence with
signature (0^15, 5177198, 0^15, -1) (fifteen zeros, `5177198`, fifteen zeros, `-1`),
that is, `a(n) = 5177198 * a(n-16) - a(n-32)`.

Conventions:
* `a n` is the denominator of the `n`-th convergent of the simple continued fraction of
  `sqrt 133`, taken from Mathlib's `GenContFract.of`; the offset is 0, so
  `a 0 = 1, a 1 = 1, a 2 = 2, a 3 = 15, ...`, as in the OEIS data.
* The recurrence is stated for every index, written with `n + 32` in place of `n`.
-/

namespace OMA.S_oeis_a041243

/-- A041243: denominators of the continued fraction convergents to `sqrt 133` (offset 0). -/
noncomputable def a (n : ℕ) : ℝ := (GenContFract.of (Real.sqrt 133)).dens n

/-- The sequence satisfies the linear recurrence with signature
`(0^15, 5177198, 0^15, -1)`. -/
theorem main : ∀ n : ℕ, a (n + 32) = 5177198 * a (n + 16) - a n := by
  sorry

end OMA.S_oeis_a041243
