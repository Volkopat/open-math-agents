import Mathlib

/-!
# A320047: Barker's closed form and recurrence for the coefficients U(1, l, k)

Source: https://oeis.org/A320047
Credit: @ivillar

Consider coefficients U(m,l,k) defined by the identity
Sum_{k=1..l} Sum_{j=0..m} A302971(m,j)/A304042(m,j) * k^j * (T-k)^j
  = Sum_{k=0..m} (-1)^(m-k) * U(m,l,k) * T^k
that holds for all positive integers l, m, T. The sequence is the 2-column table read by rows
whose l-th row (l >= 1) lists U(1,l,0), U(1,l,1) (offset 1; data 5, 6, 28, 18, 81, 36, 176, 60,
325, 90, ...). Colin Barker conjectured (Aug 03 2019) the g.f.
x*(5 + 6*x + 8*x^2 - 6*x^3 - x^4) / ((1 - x)^4*(1 + x)^4),
a(n) = (4 - 4*(-1)^n - 3*(-5+(-1)^n)*n - 3*(-3+(-1)^n)*n^2 + (1+(-1)^(1+n))*n^3) / 8, and
a(n) = 4*a(n-2) - 6*a(n-4) + 4*a(n-6) - a(n-8) for n > 8.

Status: open conjecture (Colin Barker, Aug 03 2019).

Formalization notes:
* Only m = 1 occurs. Row m = 1 of A302971 is 1, 6 and row m = 1 of A304042 is 1, 1, so
  R(1,0) = 1 and R(1,1) = 6 (`R`); these are the values forced by the defining identity
  Sum_{i=0..l-1} Sum_{j=0..1} R(1,j)*(l-i)^j*i^j = l^3 of those triangles.
* The left side is the polynomial `P l` in T over ℚ; an identity of polynomials in T holding for
  all positive integers T is an identity of coefficients, so U(1,l,k) is (-1)^(1-k) times the
  coefficient of T^k in `P l` (k = 0, 1).
* Reading the table by rows, a(2l-1) = U(1,l,0) and a(2l) = U(1,l,1) for l >= 1. The values are
  taken in ℚ (they are integers). The closed form is stated for n >= 1 and the recurrence for
  n > 8, as in the entry; the generating function is not restated.
-/

namespace OMA.S_oeis_a320047

open Polynomial

/-- `R(1, j) = A302971(1, j) / A304042(1, j)` for `j = 0, 1`. -/
def R (j : ℕ) : ℚ := if j = 0 then 1 else 6

/-- The left side `Σ_{k=1..l} Σ_{j=0..1} R(1,j) k^j (T-k)^j` as a polynomial in `T`. -/
noncomputable def P (l : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.Icc 1 l, ∑ j ∈ Finset.range 2, C (R j) * C (k : ℚ) ^ j * (X - C (k : ℚ)) ^ j

/-- `U(1, l, k)`: the coefficient of `T^k` on the right side is `(-1)^(1-k) U(1, l, k)`. -/
noncomputable def U (l k : ℕ) : ℚ := (-1) ^ (1 - k) * (P l).coeff k

/-- A320047(n) (n ≥ 1): the table with rows `U(1,l,0), U(1,l,1)` read by rows. -/
noncomputable def a (n : ℕ) : ℚ := if n % 2 = 1 then U ((n + 1) / 2) 0 else U (n / 2) 1

/-- Barker's conjectured closed form (for `n ≥ 1`) and recurrence (for `n > 8`). -/
theorem main :
    (∀ n : ℕ, 0 < n → a n = (4 - 4 * (-1) ^ n - 3 * (-5 + (-1) ^ n) * (n : ℚ) -
      3 * (-3 + (-1) ^ n) * (n : ℚ) ^ 2 + (1 + (-1) ^ (1 + n)) * (n : ℚ) ^ 3) / 8) ∧
    (∀ n : ℕ, 8 < n → a n = 4 * a (n - 2) - 6 * a (n - 4) + 4 * a (n - 6) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a320047
