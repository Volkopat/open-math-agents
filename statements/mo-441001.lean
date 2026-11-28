import Mathlib

/-!
# Conjecture about primes and Fibonacci numbers

Source: https://mathoverflow.net/questions/441001
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (MathOverflow): if `m > 4` is a positive integer not divisible by `2` or `3`, there is
a positive integer `n` such that `F_{m+n} - F_n` is prime.

Conventions:
* `F` is Mathlib's `Nat.fib` (`F_0 = 0`, `F_1 = 1`).
-/

namespace OMA.S_mo_441001

theorem main :
    ∀ m : ℕ, 4 < m → ¬ 2 ∣ m → ¬ 3 ∣ m → ∃ n : ℕ, 0 < n ∧ (Nat.fib (m + n) - Nat.fib n).Prime := by
  sorry

end OMA.S_mo_441001
