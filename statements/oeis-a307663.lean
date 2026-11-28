import Mathlib

/-!
# A307663: a(n) = (n-1)!*(Sum_{i=1..n} Sum_{j=1..i} binomial(i,j)*i/j) satisfies a D-finite recurrence

Source: https://oeis.org/A307663
Credit: @cj-55m (agent: Claude Code, model claude-fable-5-2)

The entry (offset 1, data 1, 6, 41, 329, 3090, 33654, 420792, 5981688, 95782320, ...) has the name

  a(n) = (n-1)!*(Sum_{i=1..n} Sum_{j=1..i} binomial(i,j)*i/j).

and records in its FORMULA section:

  Conjectures from Robert Israel, Oct 26 2020:
  E.g.f. ((4*x^2 - 8*x + 5)*log(-x + 1))/(2*(x - 1)^2) - ((4*x^2 - 8*x + 5)*log(1 - 2*x))/(2*(x - 1)^2)
    + x*(-6 + 5*x)/(4*(x - 1)^2).
  D-finite with recurrence 2*(n+3)*(n+2)*n*(n-2)*a(n) - (n+3)*(5*n^2-6*n-17)*a(n+1)
    + (4 n^2-n-29)* a(n+2) -(n-3)*a(n+3) = 0.

(A later comment in the entry says that the e.g.f. conjecture is true; this statement is the
second conjecture, the D-finite recurrence.)

Conventions:
* The sequence has offset `1`. `a n` is defined for every natural number `n` by the formula in
  the name, evaluated in the rationals: `(n-1)!` times the sum over `1 ≤ i ≤ n` and `1 ≤ j ≤ i`
  of `binomial(i,j) * i / j` (exact rational division; all values are in fact integers, e.g.
  `a 1 = 1`, `a 2 = 6`, `a 3 = 41`). The junk value `a 0 = 0` is not used.
* The recurrence is stated for all `n ≥ 1` (all indices in the range of the offset), as an
  identity of rational numbers, exactly in the form given in the entry.
-/

namespace OMA.S_oeis_a307663

/-- A307663: `a(n) = (n-1)! * Sum_{i=1..n} Sum_{j=1..i} binomial(i,j)*i/j`, as a rational
number. -/
def a (n : ℕ) : ℚ :=
  ((n - 1).factorial : ℚ) *
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 i, (i.choose j : ℚ) * (i : ℚ) / (j : ℚ)

/-- Robert Israel's conjectured D-finite recurrence for A307663. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    2 * ((n : ℚ) + 3) * ((n : ℚ) + 2) * (n : ℚ) * ((n : ℚ) - 2) * a n
      - ((n : ℚ) + 3) * (5 * (n : ℚ) ^ 2 - 6 * (n : ℚ) - 17) * a (n + 1)
      + (4 * (n : ℚ) ^ 2 - (n : ℚ) - 29) * a (n + 2)
      - ((n : ℚ) - 3) * a (n + 3) = 0 := by
  sorry

end OMA.S_oeis_a307663
