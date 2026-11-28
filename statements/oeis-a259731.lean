import Mathlib

/-!
# A259731: Least positive integer k such that prime(k*n)-1 is a square, or 0 if no such k exists.

Source: https://oeis.org/A259731
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A259731): `a(n) > 0` for all `n > 0`, i.e. for every `n ≥ 1`
there is a positive integer `k` such that `prime(k n) - 1` is a square. This is stronger than the
conjecture that there are infinitely many primes of the form `x^2 + 1`.

Formalization notes:
* `prime(i)` is the `i`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (i - 1)`; primes are
  at least 2, so `prime(i) - 1` in `ℕ` is the integer `prime(i) - 1`.
* With this definition `a(1), ..., a(8)` = 1, 6, 1, 3, 9, 2, 1, 181, matching the data of A259731.
-/

namespace OMA.S_oeis_a259731

/-- Sun's conjecture: for every `n ≥ 1` some `prime(k n) - 1`, `k ≥ 1`, is a square. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ IsSquare (Nat.nth Nat.Prime (k * n - 1) - 1) := by
  sorry

end OMA.S_oeis_a259731
