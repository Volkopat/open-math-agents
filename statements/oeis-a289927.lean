import Mathlib

/-!
# OEIS A289927: Barker's g.f. and recurrence for the p-INVERT of floor(phi^n)

Source: https://oeis.org/A289927 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, 2017), offset 0: p-INVERT of A014217 (starting at n=1), where
p(S) = 1 - S - S^2. Comment: Suppose s = (c(0), c(1), c(2), ...) is a sequence and p(S) is a
polynomial. Let S(x) = c(0)*x + c(1)*x^2 + c(2)*x^3 + ... and T(x) = (-p(0) + 1/p(S(x)))/x. The
p-INVERT of s is the sequence t(s) of coefficients in the Maclaurin series for T(x). A014217:
a(n) = floor(phi^n), phi the golden ratio. Formula: Conjectures from Colin Barker, Aug 15 2017:
G.f.: (1 - x^2 + x^3)*(1 + x - x^3) / (1 - 3*x - 4*x^2 + 7*x^3 + 5*x^4 - 7*x^5 - 4*x^6 + 3*x^7 +
x^8). a(n) = 3*a(n-1) + 4*a(n-2) - 7*a(n-3) - 5*a(n-4) + 7*a(n-5) + 4*a(n-6) - 3*a(n-7) - a(n-8)
for n>7.

Formalization notes:
* Starting A014217 at n = 1 means c(i) = floor(phi^(i+1)), so S(x) = Sum_{k >= 1} floor(phi^k) x^k
  (as in the entry's Mathematica program), with phi = (1 + sqrt 5)/2.
* p(0) = 1, so a(n) = [x^n] T(x) is the coefficient of x^(n+1) in 1/(1 - S - S^2), computed in
  Q[[x]] (1 - S - S^2 has constant term 1, so its inverse is the power-series inverse).
* `main` is the conjunction of both conjectures: the g.f., stated as A(x) * D(x) = N(x) in Q[[x]]
  with A(x) = Sum_{n >= 0} a(n) x^n (equivalent to A = N/D since D has constant term 1), and the
  recurrence for n > 7.
* Controls proved in the proof file: a(0..3) = 1, 4, 15, 53 as in the entry.
-/

namespace OMA.S_oeis_a289927

/-- S(x) = Sum_{k >= 1} A014217(k) x^k with A014217(k) = floor(phi^k). -/
noncomputable def S : PowerSeries ℚ :=
  PowerSeries.mk (fun k => if k = 0 then 0 else ((⌊((1 + Real.sqrt 5) / 2) ^ k⌋ : ℤ) : ℚ))

/-- a(n) = [x^n] T(x) = [x^(n+1)] 1/p(S(x)) with p(S) = 1 - S - S^2. -/
noncomputable def a (n : ℕ) : ℚ := PowerSeries.coeff (n + 1) ((1 - S - S ^ 2)⁻¹)

open PowerSeries in
/-- Barker's conjectures: the g.f. and the recurrence for n > 7. -/
theorem main : (PowerSeries.mk a * (1 - 3 * X - 4 * X ^ 2 + 7 * X ^ 3 + 5 * X ^ 4 -
      7 * X ^ 5 - 4 * X ^ 6 + 3 * X ^ 7 + X ^ 8) = (1 - X ^ 2 + X ^ 3) * (1 + X - X ^ 3)) ∧
    (∀ n : ℕ, 7 < n → a n = 3 * a (n - 1) + 4 * a (n - 2) - 7 * a (n - 3) - 5 * a (n - 4) +
      7 * a (n - 5) + 4 * a (n - 6) - 3 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a289927
