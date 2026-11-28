import Mathlib

/-!
# Are all odd integers greater than 599 of the form x² + y² + z⁴ + t⁴?

Source: https://mathoverflow.net/questions/446469 (CC BY-SA 4.0).

Question (Q2 of the post, its title): is it true that for every integer `a > 299` the equation
`2a + 1 = x² + y² + z⁴ + t⁴` has a solution in integers `x, y, z, t`? Here `599 = 2·299 + 1` is
the largest odd number below `10⁷` with no such representation. Only even powers occur, so
integer solutions are the same as solutions in natural numbers. `main` states the expected yes.
-/

namespace OMA.S_mo_446469

theorem main : ∀ a : ℕ, 299 < a → ∃ x y z t : ℕ, 2 * a + 1 = x ^ 2 + y ^ 2 + z ^ 4 + t ^ 4 := by
  sorry

end OMA.S_mo_446469
