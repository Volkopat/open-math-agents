import Mathlib

/-!
# A280523: a(n) = Fibonacci(2n + 1) - n.

Source: https://oeis.org/A280523
Credit: @ShoQo

Conjecture (Peter Kagey): a(n) = A215004(2n - 2). (Nathan Fox, Jan 27 2017: "The conjecture is
true.")

Formalization notes:
* Offset 1: `a n = F(2n+1) - n` for `n ≥ 1` (data 1, 3, 10, 30, 84, ...), in `ℤ`.
* A215004: b(0) = b(1) = 1; for n > 1, b(n) = b(n-1) + b(n-2) + floor(n/2) (offset 0).
-/

namespace OMA.S_oeis_a280523

/-- a(n) = Fibonacci(2n+1) - n. -/
def a (n : ℕ) : ℤ := (Nat.fib (2 * n + 1) : ℤ) - n

/-- A215004: b(0) = b(1) = 1, b(n) = b(n-1) + b(n-2) + floor(n/2). -/
def b : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | (n + 2) => b (n + 1) + b n + ((n + 2) / 2 : ℕ)

theorem main : ∀ n : ℕ, 1 ≤ n → a n = b (2 * n - 2) := by
  sorry

end OMA.S_oeis_a280523
