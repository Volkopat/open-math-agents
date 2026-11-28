import Mathlib

/-!
# OEIS A020963: recurrence and g.f. of Sum_{k>=1} floor(2 (1+sqrt 2)^(n-k))

Source: https://oeis.org/A020963 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry, offset 1: a(n) = Sum_{k>=1} floor( 2*(1+sqrt(2))^(n-k) ). Data: 2, 6, 17, 45, 112, ...
Formula: From Chai Wah Wu, Jun 02 2016: a(n) = 3*a(n-1) - 4*a(n-3) + a(n-4) + a(n-5) for n > 5
(conjectured). G.f.: x*(x^4 - 2*x^3 + x^2 - 2)/((x - 1)^2*(x + 1)*(x^2 + 2*x - 1))
(conjectured).

Formalization notes:
* The sum runs over k = j + 1 >= 1; the exponent n - k is an integer and the power is the real
  integer power, so the terms with k > n are floors of numbers in (0, 1), equal to 0, and the
  series is a finite sum (the proof file proves summability).
* `main` is the conjunction of both conjectures: the recurrence for n > 5, and the g.f. identity
  stated as A(x) * ((x-1)^2 (x+1)(x^2+2x-1)) = x (x^4 - 2x^3 + x^2 - 2) in Q[[x]] with
  A(x) = Sum_{n >= 1} a(n) x^n (equivalent to the quotient form because the denominator has
  constant term -1).
* Controls proved in the proof file: a(1..5) = 2, 6, 17, 45, 112 as in the entry.
-/

namespace OMA.S_oeis_a020963

/-- A020963(n) = Sum_{k >= 1} floor(2 (1 + sqrt 2)^(n - k)), the index k = j + 1 running over
k >= 1. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑' j : ℕ, ⌊2 * (1 + Real.sqrt 2) ^ ((n : ℤ) - ((j : ℤ) + 1))⌋

open PowerSeries in
/-- Wu's conjectures: the recurrence for n > 5 and the g.f. -/
theorem main :
    (∀ n : ℕ, 5 < n → a n = 3 * a (n - 1) - 4 * a (n - 3) + a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((X - 1) ^ 2 * (X + 1) * (X ^ 2 + 2 * X - 1)) = X * (X ^ 4 - 2 * X ^ 3 + X ^ 2 - 2) := by
  sorry

end OMA.S_oeis_a020963
