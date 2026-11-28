import Mathlib

/-!
# OEIS A155114: odd prime plus a Fibonacci number plus twice a Fibonacci number

Source: https://oeis.org/A155114
`a n` is the number of ways to write `n` as `p + F_i + 2 F_j` with `p` an odd prime and
`F_i, F_j` positive Fibonacci numbers. Conjecture (Zhi-Wei Sun, 2008): `a n > 0` for all
`n ≥ 6` (verified up to `10^12`).

Conventions. Positive Fibonacci numbers are the values `Nat.fib k` with `k ≥ 1`;
`a n > 0` means at least one such representation exists.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a155114

theorem main :
    ∀ n : ℕ, 6 ≤ n → ∃ p i j : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ i ∧ 1 ≤ j ∧
      n = p + Nat.fib i + 2 * Nat.fib j := by
  sorry

end OMA.S_oeis_a155114
