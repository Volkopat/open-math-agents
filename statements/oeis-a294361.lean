import Mathlib

/-!
# OEIS A294361

E.g.f.: `exp(Sum_{n >= 1} sigma(n) * x^n)`.
Differentiating `A'(x) = (Sum_{n >= 1} n * sigma(n) * x^(n - 1)) * A(x)` with `A(0) = 1`
gives the defining recurrence:
`a(0) = 1`, `a(n + 1) = Sum_{j = 0..n} C(n, j) * (j + 1)! * sigma(j + 1) * a(n - j)`.

Conjectures (Peter Bala, Nov 14 2017):
1. All terms of the sequence are of the form `6 * m + 1` (i.e. `a(n) % 6 = 1`).
2. The sequence taken modulo `10` is periodic with period `5` (`a(n + 5) % 10 = a(n) % 10`).
3. For all `k >= 2` and `n >= 0`, `k` divides `a(n + k) - a(n)` (i.e. `a(n + k) ≡ a(n) [MOD k]`).
-/

namespace OMA.S_oeis_a294361

/-- Sum of positive divisors `sigma_1(m)`. -/
def sigma1 (m : ℕ) : ℕ :=
  ∑ d ∈ Nat.divisors m, d

/-- The sequence A294361, defined by the e.g.f. recurrence of `exp(Sum_{m >= 1} sigma(m) * x^m)`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ j ∈ Finset.range (n + 1),
      Nat.choose n j * (j + 1).factorial * sigma1 (j + 1) * a (n - j)
termination_by n => n
decreasing_by omega

theorem main :
    (∀ n : ℕ, a n % 6 = 1) ∧
    (∀ n : ℕ, a (n + 5) % 10 = a n % 10) ∧
    (∀ k : ℕ, 2 ≤ k → ∀ n : ℕ, a (n + k) ≡ a n [MOD k]) := by
  sorry

end OMA.S_oeis_a294361
