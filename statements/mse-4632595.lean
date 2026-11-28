import Mathlib

/-!
# Differences of Fibonacci numbers that are prime

Source: https://math.stackexchange.com/questions/4632595

Conjecture: if `m > 4` is a positive integer not divisible by `2` or `3`, there is a positive
integer `n` such that `F_{m+n} - F_n` is a prime number. Examples of `[m, n]` with the smallest
`n`: `[5, 3], [7, 3], [11, 4], [13, 5], [17, 3], …, [619, 1353]`.

Formalization notes:
* `F_k` is Mathlib's `Nat.fib k` (`F_0 = 0`, `F_1 = F_2 = 1`), matching the examples:
  `F_8 - F_3 = 21 - 2 = 19`.
* `F_{m+n} ≥ F_n`, so the natural-number subtraction is exact.
-/

namespace OMA.S_mse_4632595

/-- For every `m > 4` coprime to `6` there is `n ≥ 1` with `F_{m+n} - F_n` prime. -/
theorem main : ∀ m : ℕ, 4 < m → ¬ 2 ∣ m → ¬ 3 ∣ m →
    ∃ n : ℕ, 1 ≤ n ∧ (Nat.fib (m + n) - Nat.fib n).Prime := by
  sorry

end OMA.S_mse_4632595
