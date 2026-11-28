import Mathlib

/-!
# For every x is there m with 2x + 1 + 2m and 2x + 1 + 4m both prime?

Source: https://math.stackexchange.com/questions/1854187

Claim: for every whole number `x` there is a whole number `m` such that `2x + 1 + 2m` and
`2x + 1 + 4m` are both prime. Equivalently, for every odd `n` there is an even `y` with `n + y`
and `n + 2y` both prime. It has been checked for odd `n` up to about `6.4 · 10^6`.

Formalization notes:
* Whole numbers are taken to be `ℕ = {0, 1, 2, …}` for both `x` and `m` (the comments use
  `0 ∈ ℕ` to cover `n = 1`).
-/

namespace OMA.S_mse_1854187

/-- Every `x` has some `m` with `2x + 1 + 2m` and `2x + 1 + 4m` both prime. -/
theorem main : ∀ x : ℕ, ∃ m : ℕ, (2 * x + 1 + 2 * m).Prime ∧ (2 * x + 1 + 4 * m).Prime := by
  sorry

end OMA.S_mse_1854187
