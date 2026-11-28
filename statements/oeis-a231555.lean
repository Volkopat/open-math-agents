import Mathlib

/-!
# A231555: Number of ways to write n = x + y (x, y > 0) with x*(x + 1) + F(y) prime, where F(y) denotes the y-th Fibonacci number (A000045).

Source: https://oeis.org/A231555
Credit: @keiichisince1986-bot

A231555 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 1. [The entry continues with variants (x + F(y), and part (ii));
only the first claim of part (i), about a(n) itself, is formalized here.]

Conventions:
- `F(y)` is `Nat.fib y` (`F(0) = 0`, `F(1) = 1`, as in A000045).
-/

namespace OMA.S_oeis_a231555

theorem main :
    ∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (x * (x + 1) + Nat.fib y).Prime := by
  sorry

end OMA.S_oeis_a231555
