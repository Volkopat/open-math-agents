import Mathlib

/-!
# OEIS A095224: squarefree Fibonacci numbers with exactly n prime divisors

Source: https://oeis.org/A095224
`a n` is the least squarefree Fibonacci number with exactly `n` prime divisors. Conjecture: the
sequence is infinite, i.e. for every `n` there is a squarefree Fibonacci number with exactly
`n` prime divisors.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a095224

theorem main :
    ∀ n : ℕ, ∃ k : ℕ, 1 ≤ Nat.fib k ∧ Squarefree (Nat.fib k) ∧ (Nat.fib k).primeFactors.card = n := by
  sorry

end OMA.S_oeis_a095224
