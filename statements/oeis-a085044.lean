import Mathlib

/-!
# OEIS A085044: τ(n) + τ(k) = τ(n + k) always solvable

Source: https://oeis.org/A085044
`a n` is the smallest `k` with `τ(n) + τ(k) = τ(n + k)`, or `0` if no such number exists.
Conjecture: no entry is zero, i.e. every `n ≥ 1` admits such a `k ≥ 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a085044

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ n.divisors.card + k.divisors.card = (n + k).divisors.card := by
  sorry

end OMA.S_oeis_a085044
