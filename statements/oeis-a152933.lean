import Mathlib

/-!
# A152933: Number of sets (in the Hausdorff metric geometry) at each location between two sets defining a polygonal configuration consisting of k 6-gonal polygonal components chained with string components of length 2 as k varies.

Source: https://oeis.org/A152933
Credit: @agchua

Colin Barker (Jul 09 2020), in the formula section of A152933, verbatim:
  Conjectures from _Colin Barker_, Jul 09 2020: (Start)
  G.f.: 9*x*(2 - x) / (1 - 67*x - 9*x^2).
  a(n) = 67*a(n-1) + 9*a(n-2) for n>2.
  (End)
Offset 1. Definition: the entry's Maple program, which is the definition of the terms. With
m = 3, l = 2, F = fibonacci and L(n) = F(n-1) + F(n+1), it forms aa, b, c, d from Fibonacci
numbers, lambda, delta = (d + aa +- sqrt((d - aa)^2 + 4bc))/2, R, S as below, and returns
a(n) = R*lambda^(n-1) + S*delta^(n-1). This file transcribes it over the reals for n ≥ 1 and
sets a(0) = 0, in accordance with the factor x of the g.f. (offset 1). All Fibonacci arguments
are nonnegative here (the smallest is l - 2 = 0).
This file states both parts: the g.f. as an identity of formal power series over ℝ,
(∑ a(n) X^n) * (1 - 67X - 9X^2) = 9X(2 - X), and the recurrence for n ≥ 3 (n > 2, as printed;
all three indices are terms).
-/

namespace OMA.S_oeis_a152933

/-- The Fibonacci number F(n) (Maple's fibonacci(n)), as a real number. -/
noncomputable def fibR (n : ℕ) : ℝ := (Nat.fib n : ℝ)

/-- L(n) = F(n-1) + F(n+1), as in the Maple program (the Lucas number, for n ≥ 1). -/
noncomputable def lucR (n : ℕ) : ℝ := fibR (n - 1) + fibR (n + 1)

/-- aa(m, l) = L(2m) F(l-2) + F(2m+2) F(l-1). -/
noncomputable def aa (m l : ℕ) : ℝ :=
  lucR (2 * m) * fibR (l - 2) + fibR (2 * m + 2) * fibR (l - 1)

/-- b(m, l) = L(2m) F(l-1) + F(2m+2) F(l). -/
noncomputable def bb (m l : ℕ) : ℝ :=
  lucR (2 * m) * fibR (l - 1) + fibR (2 * m + 2) * fibR l

/-- c(m, l) = F(2m+2) F(l-2) + F(m+2)^2 F(l-1). -/
noncomputable def cc (m l : ℕ) : ℝ :=
  fibR (2 * m + 2) * fibR (l - 2) + fibR (m + 2) ^ 2 * fibR (l - 1)

/-- d(m, l) = F(2m+2) F(l-1) + F(m+2)^2 F(l). -/
noncomputable def dd (m l : ℕ) : ℝ :=
  fibR (2 * m + 2) * fibR (l - 1) + fibR (m + 2) ^ 2 * fibR l

/-- lambda(m, l) = (d + aa + sqrt((d - aa)^2 + 4bc)) * (1/2). -/
noncomputable def lamb (m l : ℕ) : ℝ :=
  (dd m l + aa m l + Real.sqrt ((dd m l - aa m l) ^ 2 + 4 * bb m l * cc m l)) * (1 / 2)

/-- delta(m, l) = (d + aa - sqrt((d - aa)^2 + 4bc)) * (1/2). -/
noncomputable def delt (m l : ℕ) : ℝ :=
  (dd m l + aa m l - Real.sqrt ((dd m l - aa m l) ^ 2 + 4 * bb m l * cc m l)) * (1 / 2)

/-- R(m, l) = ((lambda - d) L(2m) + b F(2m+2)) / (2 lambda - d - aa). -/
noncomputable def RR (m l : ℕ) : ℝ :=
  ((lamb m l - dd m l) * lucR (2 * m) + bb m l * fibR (2 * m + 2)) /
    (2 * lamb m l - dd m l - aa m l)

/-- S(m, l) = ((lambda - aa) L(2m) - b F(2m+2)) / (2 lambda - d - aa). -/
noncomputable def SS (m l : ℕ) : ℝ :=
  ((lamb m l - aa m l) * lucR (2 * m) - bb m l * fibR (2 * m + 2)) /
    (2 * lamb m l - dd m l - aa m l)

/-- A152933(n) for n ≥ 1: the value R*lambda^(n-1) + S*delta^(n-1) of the entry's Maple program
(m = 3, l = 2); a(0) = 0. -/
noncomputable def a (n : ℕ) : ℝ :=
  if n = 0 then 0 else RR 3 2 * lamb 3 2 ^ (n - 1) + SS 3 2 * delt 3 2 ^ (n - 1)

/-- Colin Barker's conjectures: a(n) = 67a(n-1) + 9a(n-2) for n > 2, and the g.f.
9x(2 - x)/(1 - 67x - 9x^2). -/
theorem main : (∀ n : ℕ, 3 ≤ n → a n = 67 * a (n - 1) + 9 * a (n - 2)) ∧
    PowerSeries.mk a * (1 - 67 * PowerSeries.X - 9 * PowerSeries.X ^ 2) =
      9 * PowerSeries.X * (2 - PowerSeries.X) := by
  sorry

end OMA.S_oeis_a152933
