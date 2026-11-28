import Mathlib

/-!
# OEIS A048330: Mathar's g.f. and recurrence for the base-5 repdigits

Source: https://oeis.org/A048330 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Patrick De Geest, Feb 15 1999), offset 0: Numbers that are repdigits in base 5. The formula
section states: Conjecture: G.f.: x*(1+2*x+3*x^2+4*x^3) / ( (x-1)*(1+x)*(x^2+1)*(5*x^4-1) ) with
a(n) = 6*a(n-4) - 5*a(n-8). - R. J. Mathar, Mar 15 2015

Formalization notes:
* A repdigit in base 5 is a number whose base-5 digits are all equal. 0, which has no digits, is
  included, as in the entry (a(0) = 0), and so are 1, 2, 3, 4.
* With offset 0, a(n) is `Nat.nth Rep n`.
* The recurrence has no stated range; it is taken for n >= 8, the indices for which a(n-8) is a
  term.
* `main` is the conjunction of the g.f. and the recurrence. The g.f. is the series
  Sum_{n >= 0} a(n) x^n; the identity A(x) = N(x)/D(x) is stated as A(x)*D(x) = N(x) in Q[[x]],
  which is equivalent because D has constant term 1.
* Controls: the definitions give a(0..9) = 0, 1, 2, 3, 4, 6, 12, 18, 24, 31 and a(12) = 124,
  a(13) = 156, a(20) = 3124, as in the entry.
-/

namespace OMA.S_oeis_a048330

/-- `m` is a repdigit in base 5: all its base-5 digits are equal. -/
def Rep (m : ℕ) : Prop := ∀ x ∈ Nat.digits 5 m, ∀ y ∈ Nat.digits 5 m, x = y

/-- A048330 (offset 0): the `n`-th base-5 repdigit, in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth Rep n

open PowerSeries in
/-- Mathar's conjecture: the g.f., with a(n) = 6*a(n-4) - 5*a(n-8) for n >= 8. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) * (1 + X) * (X ^ 2 + 1) * (5 * X ^ 4 - 1)) =
      X * (1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3) ∧
    ∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 6 * a (n - 4) - 5 * a (n - 8) := by
  sorry

end OMA.S_oeis_a048330
