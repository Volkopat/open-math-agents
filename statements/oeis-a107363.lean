import Mathlib

/-!
# A107363: Expansion of (1 - x)*(1 + x)^2*(1 + x^2)*(1 - x^2 + 2*x^3 + x^4) / ((1 - x^2 - x^4)*(1 + x^2 + 2*x^4 - x^6 + x^8)).

Source: https://oeis.org/A107363
Credit: @avivorly

A107363 (offset 0): the coefficients of the power series
`(1 - x)(1 + x)^2(1 + x^2)(1 - x^2 + 2x^3 + x^4) / ((1 - x^2 - x^4)(1 + x^2 + 2x^4 - x^6 + x^8))`:
1, 1, -1, 1, 2, 0, 5, 3, -7, 3, 8, 0, 21, 13, -29, 13, 34, 0, ...

Conjectures (Creighton Dement, May 24 2005):
- `{ Fib(n) | n in naturals } = { a(n) | n in naturals, a(n) >= 0 } = { a(n) | n in naturals, n not of the
  form 6*n+2 }` (naturals include 0);
- `a(6*n+2) = - A048876(n)` (Generalized Pellian with second term of 7).

All of them are stated, as a conjunction; the chain of two set equalities is stated as two equalities
with the Fibonacci set.

Conventions:
- The power series live in `ℤ⟦X⟧`. The denominator has constant term 1, so `invOfUnit den 1` is its
  inverse, and `a n` is the coefficient of `x^n` in `num * (den)⁻¹`.
- `Nat.fib` is Mathlib's Fibonacci sequence (`Fib(0) = 0`, `Fib(1) = 1`); the sets are sets of integers.
- A048876 is `b 0 = 1`, `b 1 = 7`, `b n = 4 b (n-1) + b (n-2)`, as in its OEIS definition.
-/

namespace OMA.S_oeis_a107363

open PowerSeries

/-- The numerator `(1 - x)(1 + x)^2(1 + x^2)(1 - x^2 + 2x^3 + x^4)`. -/
noncomputable def num : ℤ⟦X⟧ :=
  (1 - X) * (1 + X) ^ 2 * (1 + X ^ 2) * (1 - X ^ 2 + 2 * X ^ 3 + X ^ 4)

/-- The denominator `(1 - x^2 - x^4)(1 + x^2 + 2x^4 - x^6 + x^8)`, with constant term 1. -/
noncomputable def den : ℤ⟦X⟧ :=
  (1 - X ^ 2 - X ^ 4) * (1 + X ^ 2 + 2 * X ^ 4 - X ^ 6 + X ^ 8)

/-- A107363 (offset 0): the coefficient of `x^n` in `num / den`. -/
noncomputable def a (n : ℕ) : ℤ := coeff n (num * invOfUnit den 1)

/-- A048876: `b 0 = 1`, `b 1 = 7`, `b (n + 2) = 4 * b (n + 1) + b n`. -/
def b : ℕ → ℤ
  | 0 => 1
  | 1 => 7
  | n + 2 => 4 * b (n + 1) + b n

theorem main :
    Set.range (fun n : ℕ => (Nat.fib n : ℤ)) = {x : ℤ | ∃ n : ℕ, a n = x ∧ 0 ≤ x} ∧
    Set.range (fun n : ℕ => (Nat.fib n : ℤ)) = {x : ℤ | ∃ n : ℕ, n % 6 ≠ 2 ∧ a n = x} ∧
    ∀ n : ℕ, a (6 * n + 2) = - b n := by
  sorry

end OMA.S_oeis_a107363
