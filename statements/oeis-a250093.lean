import Mathlib

/-!
# A250093: Squarefree part of Fibonacci(n^2)

Source: https://oeis.org/A250093

Conjecture (OEIS A250093):
The only prime numbers occurring in the sequence of squarefree parts of
`Fibonacci(n ^ 2)` (`n ≥ 1`) are `3` (for `n = 2`, `Fib(4) = 3`) and
`3001` (for `n = 5`, `Fib(25) = 75025 = 3001 * 5^2`).

Conventions:
- Since every prime `p` is squarefree, the squarefree part of a positive integer `m`
  equals `p` if and only if `m = p * k ^ 2` for some positive integer `k`.
-/

namespace OMA.S_oeis_a250093

/-- Conjecture: if the squarefree part of `Fib(n ^ 2)` (`n ≥ 1`) is a prime `p`,
then `p = 3` or `p = 3001`. -/
theorem main :
    ∀ n p k : ℕ, 1 ≤ n → Nat.Prime p → 1 ≤ k →
      Nat.fib (n ^ 2) = p * k ^ 2 → p = 3 ∨ p = 3001 := by
  sorry

end OMA.S_oeis_a250093
