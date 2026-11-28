import Mathlib

/-!
# Is the exponential function in a C*-algebra injective on self-adjoint elements?

Source: https://mathoverflow.net/questions/185536
Credit: @Sergei Akbarov

Let `A` be a C*-algebra and `exp x = ∑ xⁿ / n!` the usual exponential function from `A` into
`A`. Question: is it true that if `x ≠ y` are self-adjoint elements of `A`, then
`exp x ≠ exp y`?

Formalization notes:
* `A` is a unital complex C*-algebra (`CStarAlgebra A`); a unit is needed for the power series
  `∑ xⁿ / n!` to make sense (its `n = 0` term is `1`).
* `exp` is Mathlib's power-series exponential `NormedSpace.exp`.
-/

universe u

namespace OMA.S_mo_185536

/-- The exponential map of a unital C*-algebra is injective on self-adjoint elements. -/
theorem main : ∀ (A : Type u) [CStarAlgebra A] (x y : A), IsSelfAdjoint x → IsSelfAdjoint y →
    x ≠ y → NormedSpace.exp x ≠ NormedSpace.exp y := by
  sorry

end OMA.S_mo_185536
