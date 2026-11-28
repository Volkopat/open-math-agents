import Mathlib

/-!
# OEIS A221212: Barker's conjectures for the rounded areas in the unit golden spiral

Source: https://oeis.org/A221212 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A221212 (Kival Ngaokrajang, Feb 21 2013), offset 1: Rounded area of distinct right
triangles appearing in the unit golden spiral.
Data: 1, 3, 4, 7, 9, 18, 25, 47, 65, 123, 170, 322, ...
Comment: a(n) = round(x(n)), with x(1) = 1, x(2n) = F(2n)*phi + F(2n-1) and x(2n+1) = x(2n) +
x(2n-2), phi the golden ratio. Mathematica (Zak Seidov): x[1]=1; x[2]=GoldenRatio+1;
x[3]=GoldenRatio+2; x[n] = If[EvenQ[n], Fibonacci[n]*GoldenRatio+Fibonacci[n-1], x[n-1]+x[n-3]]
for n >= 4; Table[Round[x[n]], {n, m}].
Formula section:
Conjecture: a(n) = 3*a(n-2)-a(n-4) for n>5. G.f.: -x*(x+1)*(x^7-x^6-x^5+x^4+x^3+x^2-2*x-1) /
((x^2-x-1)*(x^2+x-1)). - Colin Barker, Mar 12 2013

Formalization notes:
* `x` follows the entry's Mathematica program (which reproduces the data; checked to n = 25
  with 80-digit arithmetic): x(1) = 1, x(2) = phi + 1, x(3) = phi + 2, x(n) = F(n) phi + F(n-1)
  for even n >= 4 and x(n) = x(n-1) + x(n-3) for odd n >= 5. a(n) = round(x(n)) (no x(n) is a
  half-integer: x(n) is u + v phi with v a nonzero integer).
* The entry starts at n = 1 and the g.f. starts at x^1; a 0 is set to 0 (x 0 = 0), the
  coefficient of x^0, and the g.f. is stated for mk a over the integers as A * D = N (D has
  constant term 1).
* The statement is the conjunction of Barker's recurrence (for n > 5, in the integers) and g.f.
-/

namespace OMA.S_oeis_a221212

open PowerSeries

/-- The values x(n) of the entry's program (x 0 = 0 is a placeholder for the term the entry
does not have). -/
noncomputable def x : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => Real.goldenRatio + 1
  | 3 => Real.goldenRatio + 2
  | n + 4 =>
    if (n + 4) % 2 = 0 then (Nat.fib (n + 4) : ℝ) * Real.goldenRatio + Nat.fib (n + 3)
    else x (n + 3) + x (n + 1)

/-- A221212(n) = round(x(n)). -/
noncomputable def a (n : ℕ) : ℤ := round (x n)

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 2) - a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((X ^ 2 - X - 1) * (X ^ 2 + X - 1)) =
      (- X * (X + 1) * (X ^ 7 - X ^ 6 - X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 - 2 * X - 1) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a221212
