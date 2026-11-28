import Mathlib

/-!
# For every n ≥ 2 is there k ≤ n with n + k and nk + 1 both prime?

Source: https://math.stackexchange.com/questions/5099977

Conjecture: for every integer `n ≥ 2` there is an integer `k` with `1 ≤ k ≤ n` such that
`n + k` and `n k + 1` are both prime. It has been checked for `n` up to `10^7`.

Formalization notes:
* `main` states the conjecture as written, with `n k : ℕ`.
-/

namespace OMA.S_mse_5099977

/-- Every `n ≥ 2` has some `1 ≤ k ≤ n` with `n + k` and `n * k + 1` prime. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ (n + k).Prime ∧ (n * k + 1).Prime := by
  sorry

end OMA.S_mse_5099977
