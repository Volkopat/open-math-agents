import Mathlib

/-!
# OEIS A255807

Expansion of e.g.f. `exp(Sum_{k >= 1} k^2 * x^k)`.
Differentiating `A'(x) = (Sum_{k >= 1} k^3 * x^(k - 1)) * A(x)` with `A(0) = 1` gives:
`a(0) = 1`, `a(n + 1) = Sum_{j = 0..n} C(n, j) * (j + 1)! * (j + 1)^2 * a(n - j)`.

Conjectures (Peter Bala):
1. The sequence taken modulo `10` is periodic with period `5` (`a(n + 5) % 10 = a(n) % 10`).
2. For all `k >= 2` and `n >= 0`, `k` divides `a(n + k) - a(n)` (`a(n + k) ≡ a(n) [MOD k]`).
-/

namespace OMA.S_oeis_a255807

/-- The sequence A255807, defined by the e.g.f. recurrence of `exp(Sum_{k >= 1} k^2 * x^k)`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ j ∈ Finset.range (n + 1),
      Nat.choose n j * (j + 1).factorial * (j + 1) ^ 2 * a (n - j)
termination_by n => n
decreasing_by omega

theorem main :
    (∀ n : ℕ, a (n + 5) % 10 = a n % 10) ∧
    (∀ k : ℕ, 2 ≤ k → ∀ n : ℕ, a (n + k) ≡ a n [MOD k]) := by
  sorry

end OMA.S_oeis_a255807
