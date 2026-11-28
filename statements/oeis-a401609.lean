import Mathlib

/-!
# A401609: Number of distinct primes of the form P(n)/d - d, where P(n) is the n-th primorial A002110(n) and d<prime(n) is a divisor of P(n).

Source: https://oeis.org/A401609
Credit: @gblacher2

Conjecture (OEIS A401609): a(n) > 0 except for n = 1 and n = 32.

OEIS indexes from 1: `prime n` is the `n`-th prime and `P n` is the product of the first `n`
primes. Mathlib's `Nat.nth Nat.Prime` starts at index 0. The difference `P(n)/d - d` is taken
in `ℤ`; `d` ranges over the positive divisors of `P n` below `prime n`.
-/

namespace OMA.S_oeis_a401609

open scoped BigOperators

/-- The `n`-th prime, 1-indexed: `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- A002110(n), the product of the first `n` primes: `P 0 = 1`, `P 1 = 2`, `P 2 = 6`. -/
noncomputable def P (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.range n, Nat.nth Nat.Prime k

/-- A401609(n): the number of distinct primes `P(n)/d - d` with `d ∣ P(n)` and `d < prime n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {r : ℕ | r.Prime ∧ ∃ d : ℕ, d ∣ P n ∧ d < prime n ∧
    (r : ℤ) = ((P n / d : ℕ) : ℤ) - (d : ℤ)}.ncard

theorem main : ∀ n : ℕ, 1 ≤ n → (0 < a n ↔ n ≠ 1 ∧ n ≠ 32) := by
  sorry

end OMA.S_oeis_a401609
