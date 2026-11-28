import Mathlib

/-!
# A152934: Number of sets (in the Hausdorff metric geometry) at each location between two sets defining a polygonal configuration consisting of two m-gonal polygonal components chained with string components of length 3 as m varies.

Source: https://oeis.org/A152934
Credit: @agchua

Colin Barker (Jul 09 2020), in the formula section of A152934, verbatim:
  Conjectures from _Colin Barker_, Jul 09 2020: (Start)
  G.f.: x^2*(289 - 350*x + 45*x^2) / ((1 - x)*(1 - 7*x + x^2)).
  a(n) = 8*a(n-1) - 8*a(n-2) + a(n-3) for n>4.
  (End)
Offset 2. Definition: the entry's Maple program, which is the definition of the terms. With
k = 2, l = 3, F = fibonacci and L(t) = F(t-1) + F(t+1), it forms aa(n, l), b(n, l), c(n, l),
d(n, l) from Fibonacci numbers, lambda, delta = (d + aa +- sqrt((d - aa)^2 + 4bc))/2, R, S as
below, and returns a(n) = R(n,l)*lambda(n,l)^(k-1) + S(n,l)*delta(n,l)^(k-1); here k - 1 = 1.
All Fibonacci arguments are nonnegative for n >= 2 (the smallest are l - 2 = 1 and 2n - 1).
This file transcribes the program over the reals for n >= 2 and sets a(0) = a(1) = 0, in
accordance with the factor x^2 of the g.f. (offset 2).
This file states both parts: the g.f. as an identity of formal power series over ℝ,
(∑ a(n) X^n) * ((1 - X)(1 - 7X + X^2)) = X^2 (289 - 350X + 45X^2), and the recurrence for
n >= 5 (n > 4, as printed; all four indices are terms).
-/

namespace OMA.S_oeis_a152934

/-- The Fibonacci number F(n) (Maple's fibonacci(n)), as a real number. -/
noncomputable def fibR (n : ℕ) : ℝ := (Nat.fib n : ℝ)

/-- L(n) = F(n-1) + F(n+1), as in the Maple program (the Lucas number, for n ≥ 1). -/
noncomputable def lucR (n : ℕ) : ℝ := fibR (n - 1) + fibR (n + 1)

/-- aa(n, l) = L(2n) F(l-2) + F(2n+2) F(l-1). -/
noncomputable def aa (n l : ℕ) : ℝ :=
  lucR (2 * n) * fibR (l - 2) + fibR (2 * n + 2) * fibR (l - 1)

/-- b(n, l) = L(2n) F(l-1) + F(2n+2) F(l). -/
noncomputable def bb (n l : ℕ) : ℝ :=
  lucR (2 * n) * fibR (l - 1) + fibR (2 * n + 2) * fibR l

/-- c(n, l) = F(2n+2) F(l-2) + F(n+2)^2 F(l-1). -/
noncomputable def cc (n l : ℕ) : ℝ :=
  fibR (2 * n + 2) * fibR (l - 2) + fibR (n + 2) ^ 2 * fibR (l - 1)

/-- d(n, l) = F(2n+2) F(l-1) + F(n+2)^2 F(l). -/
noncomputable def dd (n l : ℕ) : ℝ :=
  fibR (2 * n + 2) * fibR (l - 1) + fibR (n + 2) ^ 2 * fibR l

/-- lambda(n, l) = (d + aa + sqrt((d - aa)^2 + 4bc)) * (1/2). -/
noncomputable def lamb (n l : ℕ) : ℝ :=
  (dd n l + aa n l + Real.sqrt ((dd n l - aa n l) ^ 2 + 4 * bb n l * cc n l)) * (1 / 2)

/-- delta(n, l) = (d + aa - sqrt((d - aa)^2 + 4bc)) * (1/2). -/
noncomputable def delt (n l : ℕ) : ℝ :=
  (dd n l + aa n l - Real.sqrt ((dd n l - aa n l) ^ 2 + 4 * bb n l * cc n l)) * (1 / 2)

/-- R(n, l) = ((lambda - d) L(2n) + b F(2n+2)) / (2 lambda - d - aa). -/
noncomputable def RR (n l : ℕ) : ℝ :=
  ((lamb n l - dd n l) * lucR (2 * n) + bb n l * fibR (2 * n + 2)) /
    (2 * lamb n l - dd n l - aa n l)

/-- S(n, l) = ((lambda - aa) L(2n) - b F(2n+2)) / (2 lambda - d - aa). -/
noncomputable def SS (n l : ℕ) : ℝ :=
  ((lamb n l - aa n l) * lucR (2 * n) - bb n l * fibR (2 * n + 2)) /
    (2 * lamb n l - dd n l - aa n l)

/-- A152934(n) for n ≥ 2: the value R(n,3)*lambda(n,3)^(k-1) + S(n,3)*delta(n,3)^(k-1) of the
entry's Maple program, with k = 2; a(0) = a(1) = 0. -/
noncomputable def a (n : ℕ) : ℝ :=
  if n < 2 then 0 else RR n 3 * lamb n 3 ^ 1 + SS n 3 * delt n 3 ^ 1

/-- Colin Barker's conjectures: a(n) = 8a(n-1) - 8a(n-2) + a(n-3) for n > 4, and the g.f.
x^2(289 - 350x + 45x^2)/((1 - x)(1 - 7x + x^2)). -/
theorem main : (∀ n : ℕ, 5 ≤ n → a n = 8 * a (n - 1) - 8 * a (n - 2) + a (n - 3)) ∧
    PowerSeries.mk a * ((1 - PowerSeries.X) * (1 - 7 * PowerSeries.X + PowerSeries.X ^ 2)) =
      PowerSeries.X ^ 2 * (289 - 350 * PowerSeries.X + 45 * PowerSeries.X ^ 2) := by
  sorry

end OMA.S_oeis_a152934
