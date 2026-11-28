import Mathlib

/-!
# Algebraic integer with conjugates on the unit circle

Source: https://mathoverflow.net/questions/202224
Credit: @ivillar

Let $\alpha$ be an algebraic integer on the unit circle in $\mathbb{C}$ such that all the
conjugates of $\alpha$ lie on the unit circle. Does it follow that $\alpha$ is a root of unity?

Formalization notes:
* `α` is a complex number that is integral over `ℤ`.
* The conjugates of `α` are the complex roots of its minimal polynomial over `ℚ`; `α` is one of
  them, so the hypothesis also says that `α` itself lies on the unit circle.
* "Root of unity" is stated as `α ^ n = 1` for some positive `n`.
-/

namespace OMA.S_mo_202224

/-- An algebraic integer all of whose conjugates lie on the unit circle is a root of unity. -/
theorem main : ∀ α : ℂ, IsIntegral ℤ α →
    (∀ β : ℂ, Polynomial.aeval β (minpoly ℚ α) = 0 → ‖β‖ = 1) →
    ∃ n : ℕ, 0 < n ∧ α ^ n = 1 := by
  sorry

end OMA.S_mo_202224
