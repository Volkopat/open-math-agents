import Mathlib

/-!
# A049997: Numbers of the form Fibonacci(i)*Fibonacci(j).

Source: https://oeis.org/A049997
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a049997

/-- `m` is a perfect power: `m = b ^ k` with `k ≥ 2`. -/
def IsPerfectPower' (m : ℕ) : Prop := ∃ b k : ℕ, 2 ≤ k ∧ m = b ^ k

/-- Conjecture (Zhi-Wei Sun, Jan 2025; verified for 2 < m < n <= 900): for 2 < m < n, the product
`Fibonacci m * Fibonacci n` is a perfect power only for `(m, n) = (3, 6)` (where it is `2 * 8 = 2^4`). -/
theorem main : ∀ m n : ℕ, 2 < m → m < n →
    (IsPerfectPower' (Nat.fib m * Nat.fib n) ↔ (m = 3 ∧ n = 6)) := by
  sorry

end OMA.S_oeis_a049997
