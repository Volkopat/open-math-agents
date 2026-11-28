import Mathlib

/-!
# A279884: (prime(n) - 1)^(prime(n) + 1) + 1

Source: https://oeis.org/A279884

Conjecture (OEIS A279884):
If `n ≥ 1` and `(n - 1)^(n + 1) + 1` is prime, then `n` must be prime.

Conventions:
- Offset: `1`.
- Small `n ≥ 1` for which `(n - 1)^(n + 1) + 1` is prime: `n = 2, 3, 31, ...` (all prime).
- Requiring `1 ≤ n` ensures natural-number subtraction `n - 1` is exact.
-/

namespace OMA.S_oeis_a279884

/-- The expression `(n - 1)^(n + 1) + 1` associated with OEIS A279884. -/
def f (n : ℕ) : ℕ :=
  (n - 1) ^ (n + 1) + 1

/-- Conjecture: for `n ≥ 1`, if `(n - 1)^(n + 1) + 1` is prime, then `n` is prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → Nat.Prime (f n) → Nat.Prime n := by
  sorry

end OMA.S_oeis_a279884
