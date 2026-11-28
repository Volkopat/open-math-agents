import Mathlib

/-!
# A389835: Numbers k such that wt(Fibonacci(k)) * e > k, where wt(x) is the binary weight of x (A000120), and e is the natural logarithm base.

Source: https://oeis.org/A389835
Credit: @luciusacarr

Data: 1, 2, 4, 5, 7, 8, 10, 13, 14, 16, 17, 20, 23, 27, 28, ...

Conjecture (from the entry): the sequence is finite, and 4366 is the last term. `main` states it.

Reading of the source:
* `wt(x)` is the number of 1's in the binary expansion of `x`, the sum of its base-2 digits.
* `Fibonacci(k)` is `Nat.fib k` (F(1) = F(2) = 1); `k` ranges over the positive integers.
* "Finite, and 4366 is the last term" is stated as: 4366 is a term, and every term is at most
  4366 (the terms up to 20000 were recomputed; the last is 4366).
-/

namespace OMA.S_oeis_a389835

/-- The binary weight of `x` (A000120). -/
def wt (x : ℕ) : ℕ := (Nat.digits 2 x).sum

/-- The terms of A389835. -/
def S : Set ℕ := {k | 0 < k ∧ (k : ℝ) < (wt (Nat.fib k) : ℝ) * Real.exp 1}

theorem main :
    -- The sequence is finite and 4366 is its last term.
    4366 ∈ S ∧ ∀ k ∈ S, k ≤ 4366 := by
  sorry

end OMA.S_oeis_a389835
