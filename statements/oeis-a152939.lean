import Mathlib

/-!
# A152939: Number of sets (in the Hausdorff metric geometry) at each location between two sets defining a polygonal configuration consisting of four 4-gonal polygonal components chained with string components of length l as l varies.

Source: https://oeis.org/A152939
Credit: @agchua

Colin Barker (Jul 09 2020), in the formula section of A152939, verbatim:
  Conjectures from _Colin Barker_, Jul 09 2020: (Start)
  G.f.: x*(29153 + 22190*x - 17480*x^2 - 4977*x^3) / ((1 + x - x^2)*(1 - 4*x - x^2)).
  a(n) = 3*a(n-1) + 6*a(n-2) - 3*a(n-3) - a(n-4) for n>4.
  (End)
Offset 1. Definition: the entry's Maple program, which is the definition of the terms. With
k = 4, m = 2, F = fibonacci and L(t) = F(t-1) + F(t+1), it forms aa, b, c, d from Fibonacci
numbers at the location n, lambda, delta = (d + aa +- sqrt((d - aa)^2 + 4bc))/2, R, S as below,
and returns a(n) = R*lambda^(k-1) + S*delta^(k-1), here with k - 1 = 3. The arguments of F are
integers: for n = 1 the program uses F(n-2) = F(-1), and Maple's fibonacci extends F to negative
arguments by F(-s) = (-1)^(s+1) F(s), so F(-1) = 1 (this gives the first term 29153; F(-1) = 0
would give 5184). This file transcribes the program over the reals for n ≥ 1, with F defined on
the integers in the same way, and sets a(0) = 0, in accordance with the factor x of the g.f.
(offset 1). Both parts are stated: the g.f. as an identity of formal power series over ℝ,
(∑ a(n) X^n) * ((1 + X - X^2)(1 - 4X - X^2)) = X * (29153 + 22190X - 17480X^2 - 4977X^3), and the
recurrence for n > 4 as printed (all five indices are then terms).
-/

namespace OMA.S_oeis_a152939

/-- Maple's fibonacci(t) for an integer t, as a real number: F(t) for t ≥ 0, and
F(t) = (-1)^(s+1) F(s) for t = -s < 0. -/
noncomputable def fibR (t : ℤ) : ℝ :=
  if 0 ≤ t then (Nat.fib t.toNat : ℝ) else (-1) ^ ((-t).toNat + 1) * (Nat.fib (-t).toNat : ℝ)

/-- L(t) = F(t-1) + F(t+1), as in the Maple program. -/
noncomputable def lucR (t : ℤ) : ℝ := fibR (t - 1) + fibR (t + 1)

/-- aa(m, l) = L(2m) F(l-2) + F(2m+2) F(l-1). -/
noncomputable def aa (m l : ℤ) : ℝ :=
  lucR (2 * m) * fibR (l - 2) + fibR (2 * m + 2) * fibR (l - 1)

/-- b(m, l) = L(2m) F(l-1) + F(2m+2) F(l). -/
noncomputable def bb (m l : ℤ) : ℝ :=
  lucR (2 * m) * fibR (l - 1) + fibR (2 * m + 2) * fibR l

/-- c(m, l) = F(2m+2) F(l-2) + F(m+2)^2 F(l-1). -/
noncomputable def cc (m l : ℤ) : ℝ :=
  fibR (2 * m + 2) * fibR (l - 2) + fibR (m + 2) ^ 2 * fibR (l - 1)

/-- d(m, l) = F(2m+2) F(l-1) + F(m+2)^2 F(l). -/
noncomputable def dd (m l : ℤ) : ℝ :=
  fibR (2 * m + 2) * fibR (l - 1) + fibR (m + 2) ^ 2 * fibR l

/-- lambda(m, l) = (d + aa + sqrt((d - aa)^2 + 4bc)) * (1/2). -/
noncomputable def lamb (m l : ℤ) : ℝ :=
  (dd m l + aa m l + Real.sqrt ((dd m l - aa m l) ^ 2 + 4 * bb m l * cc m l)) * (1 / 2)

/-- delta(m, l) = (d + aa - sqrt((d - aa)^2 + 4bc)) * (1/2). -/
noncomputable def delt (m l : ℤ) : ℝ :=
  (dd m l + aa m l - Real.sqrt ((dd m l - aa m l) ^ 2 + 4 * bb m l * cc m l)) * (1 / 2)

/-- R(m, l) = ((lambda - d) L(2m) + b F(2m+2)) / (2 lambda - d - aa). -/
noncomputable def RR (m l : ℤ) : ℝ :=
  ((lamb m l - dd m l) * lucR (2 * m) + bb m l * fibR (2 * m + 2)) /
    (2 * lamb m l - dd m l - aa m l)

/-- S(m, l) = ((lambda - aa) L(2m) - b F(2m+2)) / (2 lambda - d - aa). -/
noncomputable def SS (m l : ℤ) : ℝ :=
  ((lamb m l - aa m l) * lucR (2 * m) - bb m l * fibR (2 * m + 2)) /
    (2 * lamb m l - dd m l - aa m l)

/-- A152939(n) for n ≥ 1: the value R*lambda^(k-1) + S*delta^(k-1) of the entry's Maple program
(k = 4, m = 2, at the location n); a(0) = 0. -/
noncomputable def a (n : ℕ) : ℝ :=
  if n = 0 then 0 else RR 2 (n : ℤ) * lamb 2 (n : ℤ) ^ 3 + SS 2 (n : ℤ) * delt 2 (n : ℤ) ^ 3

/-- Colin Barker's conjectures: a(n) = 3a(n-1) + 6a(n-2) - 3a(n-3) - a(n-4) for n > 4, and the
g.f. x(29153 + 22190x - 17480x^2 - 4977x^3)/((1 + x - x^2)(1 - 4x - x^2)). -/
theorem main : (∀ n : ℕ, 5 ≤ n →
      a n = 3 * a (n - 1) + 6 * a (n - 2) - 3 * a (n - 3) - a (n - 4)) ∧
    PowerSeries.mk a * ((1 + PowerSeries.X - PowerSeries.X ^ 2) *
        (1 - 4 * PowerSeries.X - PowerSeries.X ^ 2)) =
      PowerSeries.X * (29153 + 22190 * PowerSeries.X - 17480 * PowerSeries.X ^ 2 -
        4977 * PowerSeries.X ^ 3) := by
  sorry

end OMA.S_oeis_a152939
