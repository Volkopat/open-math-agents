import Mathlib

/-!
# A152932: Number of sets (in the Hausdorff metric geometry) at each location between two sets defining a polygonal configuration consisting of three 6-gonal polygonal components chained with string components of length l as l varies.

Source: https://oeis.org/A152932
Credit: @agchua

Colin Barker (Jul 09 2020), in the formula section of A152932, verbatim:
  Conjectures from _Colin Barker_, Jul 09 2020: (Start)
  G.f.: 9*x*(3637 + 1655*x - 1170*x^2) / ((1 + x)*(1 - 3*x + x^2)).
  a(n) = 2*a(n-1) + 2*a(n-2) - a(n-3) for n>3.
  (End)
Offset 1. Definition: the entry's Maple program, which is the definition of the terms. With
k = 3, m = 3, F = fibonacci and L(t) = F(t-1) + F(t+1), it forms aa(m, n), b(m, n), c(m, n),
d(m, n) from Fibonacci numbers, lambda, delta = (d + aa +- sqrt((d - aa)^2 + 4bc))/2, R, S as
below, and returns a(n) = R(m,n)*lambda(m,n)^(k-1) + S(m,n)*delta(m,n)^(k-1); here k - 1 = 2.
The program evaluates F(n-2), F(n-1), F(n), so at n = 1 it uses Maple's fibonacci(-1) = 1 (the
value with F(1) = F(0) + F(-1)); with it the program gives the listed a(1) = 32733. Below,
fibM is Maple's fibonacci on the integers t >= -1 (Nat.fib t for t >= 0, and 1 at t = -1); no
smaller argument occurs for n >= 1. This file transcribes the program over the reals for
n >= 1 and sets a(0) = 0, in accordance with the factor x of the g.f. (offset 1).
This file states both parts: the g.f. as an identity of formal power series over ℝ,
(∑ a(n) X^n) * ((1 + X)(1 - 3X + X^2)) = 9X(3637 + 1655X - 1170X^2), and the recurrence for
n >= 4 (n > 3, as printed; all four indices are terms).
-/

namespace OMA.S_oeis_a152932

/-- Maple's fibonacci(t) for integers t >= -1: Nat.fib t for t >= 0, and fibonacci(-1) = 1. -/
noncomputable def fibM (t : ℤ) : ℝ := if t = -1 then 1 else (Nat.fib t.toNat : ℝ)

/-- L(t) = F(t-1) + F(t+1), as in the Maple program. -/
noncomputable def lucM (t : ℤ) : ℝ := fibM (t - 1) + fibM (t + 1)

/-- aa(m, n) = L(2m) F(n-2) + F(2m+2) F(n-1). -/
noncomputable def aa (m n : ℤ) : ℝ :=
  lucM (2 * m) * fibM (n - 2) + fibM (2 * m + 2) * fibM (n - 1)

/-- b(m, n) = L(2m) F(n-1) + F(2m+2) F(n). -/
noncomputable def bb (m n : ℤ) : ℝ :=
  lucM (2 * m) * fibM (n - 1) + fibM (2 * m + 2) * fibM n

/-- c(m, n) = F(2m+2) F(n-2) + F(m+2)^2 F(n-1). -/
noncomputable def cc (m n : ℤ) : ℝ :=
  fibM (2 * m + 2) * fibM (n - 2) + fibM (m + 2) ^ 2 * fibM (n - 1)

/-- d(m, n) = F(2m+2) F(n-1) + F(m+2)^2 F(n). -/
noncomputable def dd (m n : ℤ) : ℝ :=
  fibM (2 * m + 2) * fibM (n - 1) + fibM (m + 2) ^ 2 * fibM n

/-- lambda(m, n) = (d + aa + sqrt((d - aa)^2 + 4bc)) * (1/2). -/
noncomputable def lamb (m n : ℤ) : ℝ :=
  (dd m n + aa m n + Real.sqrt ((dd m n - aa m n) ^ 2 + 4 * bb m n * cc m n)) * (1 / 2)

/-- delta(m, n) = (d + aa - sqrt((d - aa)^2 + 4bc)) * (1/2). -/
noncomputable def delt (m n : ℤ) : ℝ :=
  (dd m n + aa m n - Real.sqrt ((dd m n - aa m n) ^ 2 + 4 * bb m n * cc m n)) * (1 / 2)

/-- R(m, n) = ((lambda - d) L(2m) + b F(2m+2)) / (2 lambda - d - aa). -/
noncomputable def RR (m n : ℤ) : ℝ :=
  ((lamb m n - dd m n) * lucM (2 * m) + bb m n * fibM (2 * m + 2)) /
    (2 * lamb m n - dd m n - aa m n)

/-- S(m, n) = ((lambda - aa) L(2m) - b F(2m+2)) / (2 lambda - d - aa). -/
noncomputable def SS (m n : ℤ) : ℝ :=
  ((lamb m n - aa m n) * lucM (2 * m) - bb m n * fibM (2 * m + 2)) /
    (2 * lamb m n - dd m n - aa m n)

/-- A152932(n) for n ≥ 1: the value R(3,n)*lambda(3,n)^(k-1) + S(3,n)*delta(3,n)^(k-1) of the
entry's Maple program, with k = 3; a(0) = 0. -/
noncomputable def a (n : ℕ) : ℝ :=
  if n = 0 then 0 else RR 3 n * lamb 3 n ^ 2 + SS 3 n * delt 3 n ^ 2

/-- Colin Barker's conjectures: a(n) = 2a(n-1) + 2a(n-2) - a(n-3) for n > 3, and the g.f.
9x(3637 + 1655x - 1170x^2)/((1 + x)(1 - 3x + x^2)). -/
theorem main : (∀ n : ℕ, 4 ≤ n → a n = 2 * a (n - 1) + 2 * a (n - 2) - a (n - 3)) ∧
    PowerSeries.mk a * ((1 + PowerSeries.X) * (1 - 3 * PowerSeries.X + PowerSeries.X ^ 2)) =
      9 * PowerSeries.X * (3637 + 1655 * PowerSeries.X - 1170 * PowerSeries.X ^ 2) := by
  sorry

end OMA.S_oeis_a152932
