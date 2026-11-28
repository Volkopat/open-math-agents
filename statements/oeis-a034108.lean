import Mathlib

/-!
# OEIS A034108: Wu's recurrence and g.f. for the run starts of sqrt with first decimal 2

Source: https://oeis.org/A034108 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Patrick De Geest, Sep 15 1998), offset 1: Fractional part of square root of a(n) starts with
2: first term of runs. The formula section states: Conjectures from Chai Wah Wu, Apr 14 2024:
(Start) a(n) = 2*a(n-1) - a(n-2) + a(n-5) - 2*a(n-6) + a(n-7) for n > 8. G.f.: x*(-6*x^7 + 7*x^6
+ 2*x^5 - 2*x^4 - x^3 + 3*x^2 - 8*x - 5)/((x - 1)^3*(x^4 + x^3 + x^2 + x + 1)). (End)

Formalization notes:
* The fractional part of the square root of m starts with 2 when its first decimal digit
  floor(10 * frac(sqrt m)) is 2. (Reading the first nonzero digit instead would make 1158 a term,
  since sqrt 1158 = 34.029..., and 1158 is not among the listed terms.)
* The runs are the maximal runs of consecutive integers with the property; m >= 1 starts a run
  when m has the property and m - 1 does not. With offset 1, a(n) is `Nat.nth RunStart (n - 1)`.
* `main` is the conjunction of both conjectures. The g.f. is the series Sum_{n >= 1} a(n) x^n; the
  identity A(x) = N(x)/D(x) is stated as A(x)*D(x) = N(x) in Q[[x]], which is equivalent because
  D has constant term -1.
* Controls: the definitions give a(1..8) = 5, 18, 28, 39, 52, 68, 85, 105, as in the entry.
-/

namespace OMA.S_oeis_a034108

/-- The first decimal digit of the fractional part of `√m`. -/
noncomputable def digit (m : ℕ) : ℤ := ⌊10 * Int.fract (Real.sqrt m)⌋

/-- `m` starts a run: `m` has first decimal 2 and `m - 1` does not. -/
def RunStart (m : ℕ) : Prop := 0 < m ∧ digit m = 2 ∧ digit (m - 1) ≠ 2

/-- A034108 (offset 1): the `n`-th run start, in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth RunStart (n - 1)

open PowerSeries in
/-- Wu's conjectures: the recurrence for n > 8, and the g.f. -/
theorem main :
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 2 * a (n - 1) - a (n - 2) + a (n - 5) - 2 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((X - 1) ^ 3 * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X * (-6 * X ^ 7 + 7 * X ^ 6 + 2 * X ^ 5 - 2 * X ^ 4 - X ^ 3 + 3 * X ^ 2 - 8 * X - 5) := by
  sorry

end OMA.S_oeis_a034108
