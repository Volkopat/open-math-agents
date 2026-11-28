import Mathlib

/-!
# A027483: Second subdiagonal of triangle A027478, constructed from the Stirling numbers of the first kind.

Source: https://oeis.org/A027483
Credit: @agchua

Chai Wah Wu (May 07 2025), in the formula section of A027483:
  Conjectures from Chai Wah Wu, May 07 2025: (Start)
  a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7)
  - 9*a(n-8) + a(n-9) for n > 11.
  G.f.: x^3*(x^5 + 112*x^4 + 1072*x^3 + 2312*x^2 + 1367*x + 176)/(1 - x)^9. (End)
This file states both parts: the recurrence for n ≥ 12, as written, and the g.f. as an identity of
formal power series over ℚ, (X^3 * Sum_{n ≥ 0} a(n+3) X^n) * (1 - X)^9 =
X^3 * (X^5 + 112X^4 + 1072X^3 + 2312X^2 + 1367X + 176).
Definition, from the formula section and the Mathematica program of A027478: A is the lower
triangular matrix with entries A(i, j) = (-1)^(i+j) s(i, j)/i! (rows and columns i, j ≥ 1), where s is
the Stirling number of the first kind; (-1)^(i+j) s(i, j) = |s(i, j)| is the unsigned Stirling number
Nat.stirlingFirst i j, which is 0 for j > i. The triangle is T(i, j) = i!^3 (A A A)(i, j): the program
multiplies row i of m.m.m by i!^3. As A is lower triangular, the matrix product may be taken over the
indices 1..i, and that is the definition below. The second subdiagonal is a(n) = T(n, n-2) for n ≥ 3
(offset 3: 176 = T(3, 1), 2951 = T(4, 2), 22535 = T(5, 3), ...), with values taken in ℚ.
-/

namespace OMA.S_oeis_a027483

/-- The normalized unsigned Stirling matrix of the first kind: A(i, j) = |s(i, j)|/i!. -/
def A (i j : ℕ) : ℚ := (Nat.stirlingFirst i j : ℚ) / (i.factorial : ℚ)

/-- A027478: T(i, j) = i!^3 * (A^3)(i, j), the matrix product taken over the indices 1..i. -/
def T (i j : ℕ) : ℚ :=
  (i.factorial : ℚ) ^ 3 * ∑ k ∈ Finset.Icc 1 i, ∑ l ∈ Finset.Icc 1 i, A i k * A k l * A l j

/-- A027483: a(n) = T(n, n-2), n ≥ 3. -/
def a (n : ℕ) : ℚ := T n (n - 2)

/-- Wu's conjectures: the recurrence for n > 11 and the g.f.
x^3 (x^5 + 112x^4 + 1072x^3 + 2312x^2 + 1367x + 176)/(1 - x)^9. -/
theorem main :
    (∀ n : ℕ, 12 ≤ n → a n = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) +
      126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) ∧
    PowerSeries.X ^ 3 * PowerSeries.mk (fun n => a (n + 3)) * (1 - PowerSeries.X) ^ 9 =
      PowerSeries.X ^ 3 * (PowerSeries.X ^ 5 + 112 * PowerSeries.X ^ 4 + 1072 * PowerSeries.X ^ 3 +
        2312 * PowerSeries.X ^ 2 + 1367 * PowerSeries.X + 176) := by
  sorry

end OMA.S_oeis_a027483
