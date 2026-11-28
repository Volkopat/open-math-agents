import Mathlib

/-!
# A056243: Third diagonal of triangle A056242.

Source: https://oeis.org/A056243
Credit: @vivanpoddar

The sequence (offset 3) begins 1, 9, 41, 146, 456, 1312, 3568, 9312, ...
A056242 is the triangle T(n,k) of the numbers of k-part order-consecutive partitions of {1,...,n};
it is taken here through the explicit formula of that entry (formula (11) of Hwang and Mallows),
T(n,k) = Sum_{j=0..k-1} (-1)^(k-1-j)*binomial(k-1, j)*binomial(n+2j-1, 2j), and the third diagonal is
a(n) = T(n, n-2) for n >= 3 (this is the formula of Pab Ter in the present entry). For the
generating function a(n) is 0 for n < 3.

Conjecture (Colin Barker, Mar 20 2012): a(n) = 2^(-6+n)*(32-35*n+9*n^2).
G.f.: x^3*(1+3*x-x^2)/(1-2*x)^3.
The closed form is stated over the rationals for n >= 3 (the offset), the generating function as
the identity G(x) * (1-2x)^3 = x^3*(1+3x-x^2) between formal power series over the integers.
-/

namespace OMA.S_oeis_a056243

open PowerSeries

/-- The triangle of A056242, by its explicit formula. -/
def T (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range k,
    (-1) ^ (k - 1 - j) * ((k - 1).choose j : ℤ) * ((n + 2 * j - 1).choose (2 * j) : ℤ)

/-- A056243: the third diagonal T(n, n-2) for n >= 3 (and 0 for n < 3). -/
def a (n : ℕ) : ℤ := if n < 3 then 0 else T n (n - 2)

/-- The conjectured closed form and generating function for A056243. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n →
      (a n : ℚ) = (2 : ℚ) ^ ((n : ℤ) - 6) * (32 - 35 * (n : ℚ) + 9 * (n : ℚ) ^ 2)) ∧
    PowerSeries.mk a * (1 - 2 * X) ^ 3 = X ^ 3 * (1 + 3 * X - X ^ 2) := by
  sorry

end OMA.S_oeis_a056243
