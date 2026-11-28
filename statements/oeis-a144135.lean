import Mathlib

/-!
# A144135: Barker's recurrence and g.f. for the Gegenbauer values C_n^(2)(8)

Source: https://oeis.org/A144135
Credit: @ivillar

Status: known result (the OEIS entry records that the conjecture and the empirical g.f. were
verified).

A144135 (offset 0): a(n) = GegenbauerC[n,2,8], the Gegenbauer (ultraspherical) polynomial
C_n^(2)(x) evaluated at x = 8; data 1, 32, 766, 16288, 324611, ...
Conjecture (Colin Barker, Oct 27 2014): a(n) = 32*a(n-1) - 258*a(n-2) + 32*a(n-3) - a(n-4), with
empirical g.f. x / (x^2-16*x+1)^2. Robert Israel (Jul 26 2026): conjecture and empirical g.f.
verified.

Formalization notes.
* The Gegenbauer polynomials are given by the standard three-term recurrence (DLMF 18.9.1):
  C_0 = 1, C_1(x) = 2*lam*x and (n+1)*C_{n+1}(x) = 2*x*(n+lam)*C_n(x) - (n+2*lam-1)*C_{n-1}(x);
  `gegenbauer lam x n` is C_n^(lam)(x), computed in ℚ, and a(n) = C_n^(2)(8).
* The recurrence is stated for n ≥ 4, i.e. wherever all five terms exist.
* Barker's g.f. x/(x^2-16x+1)^2 = x + 32x^2 + 766x^3 + ... has a(n) as the coefficient of x^(n+1),
  i.e. it is x times Sum_{n>=0} a(n) x^n. It is stated over ℚ⟦X⟧, cross-multiplied by the
  denominator (x^2-16x+1)^2, whose constant coefficient is 1.
-/

namespace OMA.S_oeis_a144135

open PowerSeries

/-- The Gegenbauer polynomial C_n^(lam) evaluated at x, by the three-term recurrence. -/
def gegenbauer (lam x : ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => 2 * lam * x
  | n + 2 => (2 * x * ((n : ℚ) + 1 + lam) * gegenbauer lam x (n + 1) -
      ((n : ℚ) + 2 * lam) * gegenbauer lam x n) / ((n : ℚ) + 2)

/-- A144135: a(n) = C_n^(2)(8). -/
def a (n : ℕ) : ℚ := gegenbauer 2 8 n

/-- Barker's conjectures: the recurrence and the g.f. x/(x^2-16x+1)^2 (cross-multiplied). -/
theorem main :
    (∀ n : ℕ, 4 ≤ n →
      a n = 32 * a (n - 1) - 258 * a (n - 2) + 32 * a (n - 3) - a (n - 4)) ∧
    X * PowerSeries.mk a * (X ^ 2 - 16 * X + 1) ^ 2 = X := by
  sorry

end OMA.S_oeis_a144135
