import Mathlib

/-!
# Rational points on the Picard curve `y³ = x⁴ + x + 1`

Source: https://mathoverflow.net/questions/415812 (Bogdan Grechuk)
Credit: Sudharsan Rajendiran

What are (a) the integer and (b) the rational solutions of `y³ = x⁴ + x + 1`? There are the obvious
solutions `(x, y) = (-1, 1)` and `(0, 1)`; are they the only ones?

The accepted answer on the source page shows that they are: the only affine rational points are
`(-1, 1)` and `(0, 1)` (a computer-assisted proof by Chabauty–Coleman at `5` and a Mordell–Weil
sieve, for this genus-3 curve whose Jacobian has rank `2`). We state this answer for rational
solutions, which also covers part (a), since integer solutions are rational solutions.
-/

namespace OMA.S_mo_415812

/-- The only rational solutions of `y³ = x⁴ + x + 1` are `(-1, 1)` and `(0, 1)`. -/
theorem main : ∀ x y : ℚ, y ^ 3 = x ^ 4 + x + 1 → (x = -1 ∧ y = 1) ∨ (x = 0 ∧ y = 1) := by
  sorry

end OMA.S_mo_415812
