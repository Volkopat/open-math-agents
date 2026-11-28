import Mathlib

/-!
# A304822: a(n) = A304821(n + 3) / A304821(n) - 1

Source: https://oeis.org/A304822

Conjecture (OEIS A304822):
Let `A304821` be defined by `b(1) = b(2) = b(3) = 6` and
`b(n) = b(n - 3) + lcm(b(n - 3), n - 2)` for `n > 3`.
Then for every `n ≥ 1`, `a(n) = b(n + 3) / b(n) - 1` is either `1` or a prime number.

Conventions:
- Here `a304821` is `0`-indexed (`a304821 0 = 6`, `a304821 1 = 6`, `a304821 2 = 6`,
  `a304821 (n + 3) = a304821 n + Nat.lcm (a304821 n) (n + 2)`), corresponding to
  `b(n + 1)` in OEIS offset `1`.
- First terms of A304822 (`n = 0, 1, 2, ...`): `1, 1, 2, 5, 1, 7, 1, 3, 5, 11, 1, 13, 7, 5, ...`.
-/

namespace OMA.S_oeis_a304822

/-- `0`-indexed version of OEIS A304821: `b(0) = b(1) = b(2) = 6` and
`b(n + 3) = b(n) + lcm(b(n), n + 2)`. -/
def a304821 : ℕ → ℕ
  | 0 => 6
  | 1 => 6
  | 2 => 6
  | n + 3 => a304821 n + Nat.lcm (a304821 n) (n + 2)

/-- `0`-indexed version of OEIS A304822: `a304821 (n + 3) / a304821 n - 1`. -/
def a (n : ℕ) : ℕ :=
  a304821 (n + 3) / a304821 n - 1

/-- Conjecture: every term of A304822 is either `1` or prime. -/
theorem main :
    ∀ n : ℕ, a n = 1 ∨ Nat.Prime (a n) := by
  sorry

end OMA.S_oeis_a304822
