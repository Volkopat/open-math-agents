import Mathlib

/-!
# A304331: Number of integers k > 1 such that n - F(k) is a positive squarefree number

Source: https://oeis.org/A304331
Credit: @niclorusso

A304331(n) is the number of integers k > 1 such that n - F(k) is a positive squarefree number, where
F(k) denotes the k-th Fibonacci number A000045(k).

Conjecture (Zhi-Wei Sun, in the comments of A304331): a(n) > 0 for all n > 1. In other words, every
n = 2,3,... can be written as the sum of a positive Fibonacci number and a positive squarefree
number.

Conventions:
* F(k) is Mathlib's `Nat.fib k` (F(1) = F(2) = 1), with k > 1 as in the definition of a(n).
* a(n) > 0 means that n = F(k) + s for some k > 1 and some squarefree s > 0.
-/

namespace OMA.S_oeis_a304331

/-- Sun's conjecture on A304331: every `n > 1` is `F(k) + s` with `k > 1` and `s > 0` squarefree. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ k s : ℕ, 1 < k ∧ 0 < s ∧ Squarefree s ∧ Nat.fib k + s = n := by
  sorry

end OMA.S_oeis_a304331
