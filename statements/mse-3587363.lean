import Mathlib

/-!
# If n! + k is a perfect power with k > 3, must n ≤ k?

Source: https://math.stackexchange.com/questions/3587363

The asker observed that if `n! + k = a^b` with `n, k, a, b` natural numbers, `k > 3` and
`b ≥ 2`, then `n ≤ k` (checked for `k ≤ 2500` and `n ≤ 10^4`), and asks whether this always
holds, i.e. whether there is no such perfect power with `n > k`. For non-square `k` and `b = 2`
this was proved in an earlier question.

Formalization notes:
* `main` states that `n ≤ k` always holds, with all variables in `ℕ`.
-/

namespace OMA.S_mse_3587363

/-- If `n! + k = a^b` with `k > 3` and `b ≥ 2`, then `n ≤ k`. -/
theorem main : ∀ n k a b : ℕ, 3 < k → 2 ≤ b → n.factorial + k = a ^ b → n ≤ k := by
  sorry

end OMA.S_mse_3587363
