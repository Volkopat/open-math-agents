import Mathlib

/-!
# A027481: Second subdiagonal of triangle A027477, constructed from the Stirling numbers of the first kind.

Source: https://oeis.org/A027481
Credit: @agchua

Chai Wah Wu (Apr 08 2021), in the formula section of A027481:
  Conjectures from Chai Wah Wu, Apr 08 2021: (Start)
  a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n > 9.
  G.f.: x^3*(-13*x^2 - 54*x - 23)/(x - 1)^7. (End)
This file states both parts: the recurrence for n ≥ 10, as written, and the g.f. as an identity of
formal power series over ℚ, (X^3 * Sum_{n ≥ 0} a(n+3) X^n) * (X - 1)^7 = X^3 * (-13X^2 - 54X - 23).
Definition, from the formula section and the Mathematica program of A027477: A is the lower
triangular matrix with entries A(i, j) = (-1)^(i+j) s(i, j)/i! (rows and columns i, j ≥ 1), where s is
the Stirling number of the first kind; (-1)^(i+j) s(i, j) = |s(i, j)| is the unsigned Stirling number
Nat.stirlingFirst i j, which is 0 for j > i. The triangle A027477 is T(i, j) = i!^2 (A A)(i, j): the
program multiplies row i of m.m by i!^2. As A is lower triangular, the matrix product may be taken
over the indices 1..i, and that is the definition below. The second subdiagonal is a(n) = T(n, n-2)
for n ≥ 3 (offset 3: 23 = T(3, 1), 215 = T(4, 2), 1035 = T(5, 3), ..., as listed), with values
taken in ℚ. (The entry's formula line a(n) = A027477(n+2,n) counts from 1; with the entry's
offset 3 and its data the same subdiagonal is a(n) = A027477(n, n-2).)
-/

namespace OMA.S_oeis_a027481

/-- The normalized unsigned Stirling matrix of the first kind: A(i, j) = |s(i, j)|/i!. -/
def A (i j : ℕ) : ℚ := (Nat.stirlingFirst i j : ℚ) / (i.factorial : ℚ)

/-- A027477: T(i, j) = i!^2 * (A^2)(i, j), the matrix product taken over the indices 1..i. -/
def T (i j : ℕ) : ℚ :=
  (i.factorial : ℚ) ^ 2 * ∑ k ∈ Finset.Icc 1 i, A i k * A k j

/-- A027481: a(n) = T(n, n-2), n ≥ 3. -/
def a (n : ℕ) : ℚ := T n (n - 2)

/-- Wu's conjectures: the recurrence for n > 9 and the g.f. x^3 (-13x^2 - 54x - 23)/(x - 1)^7. -/
theorem main :
    (∀ n : ℕ, 10 ≤ n → a n = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
      21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.X ^ 3 * PowerSeries.mk (fun n => a (n + 3)) * (PowerSeries.X - 1) ^ 7 =
      PowerSeries.X ^ 3 * (-13 * PowerSeries.X ^ 2 - 54 * PowerSeries.X - 23) := by
  sorry

end OMA.S_oeis_a027481
