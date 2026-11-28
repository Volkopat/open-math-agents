import Mathlib

/-!
# OEIS A048331: Mathar's g.f. and recurrence for the base-6 repdigits

Source: https://oeis.org/A048331 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Patrick De Geest, Feb 15 1999), offset 0: Numbers that are repdigits in base 6. The formula
section states: Conjecture: G.f.: x*(1+2*x+3*x^2+4*x^3+5*x^4) / ( (x-1)*(x^4+x^3+x^2+x+1)*(6*x^5-1) )
with a(n) = 7*a(n-5) - 6*a(n-10). - R. J. Mathar, Mar 15 2015

Formalization notes:
* A repdigit in base 6 is a number whose base-6 digits are all equal. 0, which has no digits, is
  included, as in the entry (a(0) = 0), and so are 1, ..., 5.
* With offset 0, a(n) is `Nat.nth Rep n`.
* The recurrence has no stated range; it is taken for n >= 10, the indices for which a(n-10) is a
  term.
* `main` is the conjunction of the g.f. and the recurrence. The g.f. is the series
  Sum_{n >= 0} a(n) x^n; the identity A(x) = N(x)/D(x) is stated as A(x)*D(x) = N(x) in Q[[x]],
  which is equivalent because D has constant term 1.
* Controls: the definitions give a(0..11) = 0, 1, 2, 3, 4, 5, 7, 14, 21, 28, 35, 43 and
  a(15) = 215, as in the entry.
-/

namespace OMA.S_oeis_a048331

/-- `m` is a repdigit in base 6: all its base-6 digits are equal. -/
def Rep (m : ℕ) : Prop := ∀ x ∈ Nat.digits 6 m, ∀ y ∈ Nat.digits 6 m, x = y

/-- A048331 (offset 0): the `n`-th base-6 repdigit, in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth Rep n

open PowerSeries in
/-- Mathar's conjecture: the g.f., with a(n) = 7*a(n-5) - 6*a(n-10) for n >= 10. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) *
        ((X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (6 * X ^ 5 - 1)) =
      X * (1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 5 * X ^ 4) ∧
    ∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 7 * a (n - 5) - 6 * a (n - 10) := by
  sorry

end OMA.S_oeis_a048331
