import Mathlib

/-!
# OEIS A393172

Expansion of g.f. `A(x) = Sum_{n >= 1} a(n) * x^n` satisfying `A(x - x^2) = x + A(x)^2`.

Extracting `[x^n]` from `Sum_{k = 1..n} a(k) * x^k * (1 - x)^k = x + A(x)^2` gives
`a(0) = 0`, `a(1) = 1`, and for `n >= 2`:
`a(n) = Sum_{j = 1..n-1} a(j) * a(n - j) - Sum_{k = 1..n-1} (-1)^(n - k) * binomial(k, n - k) * a(k)`.
(First terms: `1, 2, 8, 42, 260, 1808, 13744, 112290, ...`)

Conjecture:
For all `n > 1`, `a(n) ≡ 2 (mod 4)` if `n` is a power of `2`, and `a(n) ≡ 0 (mod 4)` otherwise.
-/

namespace OMA.S_oeis_a393172

/-- Sequence A393172 defined by the recurrence from `A(x - x^2) = x + A(x)^2`. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    (∑ j : Fin (n + 1), a (j.1 + 1) * a (n + 1 - j.1)) -
      ∑ k : Fin (n + 1),
        (-1 : ℤ) ^ (n + 1 - k.1) * (Nat.choose (k.1 + 1) (n + 1 - k.1) : ℤ) * a (k.1 + 1)
termination_by n => n

theorem main :
    ∀ n : ℕ, 1 < n →
      ((∃ k : ℕ, n = 2 ^ k) → a n ≡ 2 [ZMOD 4]) ∧
      ((¬ ∃ k : ℕ, n = 2 ^ k) → a n ≡ 0 [ZMOD 4]) := by
  sorry

end OMA.S_oeis_a393172
