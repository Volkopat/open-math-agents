import Mathlib

/-!
# OEIS A294362

E.g.f.: `exp(Sum_{n >= 1} sigma_2(n) * x^n)`.
Differentiating `A'(x) = (Sum_{n >= 1} n * sigma_2(n) * x^(n - 1)) * A(x)` with `A(0) = 1`
gives the defining recurrence:
`a(0) = 1`, `a(n + 1) = Sum_{j = 0..n} C(n, j) * (j + 1)! * sigma_2(j + 1) * a(n - j)`.

Conjectures (Peter Bala, Nov 14 2017):
1. The sequence taken modulo `10` is periodic with period `(1, 1, 1, 1, 5)` of length `5`.
2. For all `k >= 2` and `n >= 0`, `k` divides `a(n + k) - a(n)` (i.e. `a(n + k) ≡ a(n) [MOD k]`).
-/

namespace OMA.S_oeis_a294362

/-- Sum of squares of positive divisors `sigma_2(m)`. -/
def sigma2 (m : ℕ) : ℕ :=
  ∑ d ∈ Nat.divisors m, d ^ 2

/-- The sequence A294362, defined by the e.g.f. recurrence of `exp(Sum_{m >= 1} sigma_2(m) * x^m)`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ j ∈ Finset.range (n + 1),
      Nat.choose n j * (j + 1).factorial * sigma2 (j + 1) * a (n - j)
termination_by n => n
decreasing_by omega

theorem main :
    (∀ n : ℕ, a (n + 5) % 10 = a n % 10) ∧
    (a 0 % 10 = 1 ∧ a 1 % 10 = 1 ∧ a 2 % 10 = 1 ∧ a 3 % 10 = 1 ∧ a 4 % 10 = 5) ∧
    (∀ k : ℕ, 2 ≤ k → ∀ n : ℕ, a (n + k) ≡ a n [MOD k]) := by
  sorry

end OMA.S_oeis_a294362
