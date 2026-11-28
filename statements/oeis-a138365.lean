import Mathlib

/-!
# A138365: the empirical generating function of A006190(n) * A006190(n+2)

Source: https://oeis.org/A138365
Credit: @ivillar

Status: known result. The OEIS entry notes that a(n) = 10*a(n-1) + 10*a(n-2) - a(n-3) for
n >= 4, and that the conjectured generating function follows from this.

A006190 (offset 0) is b(0) = 0, b(1) = 1, b(n) = 3*b(n-1) + b(n-2). A138365 (offset 1) is
a(n) = A006190(n) * A006190(n+2), with data 10, 99, 1090, 11880, 129601, ...
Colin Barker (Oct 20 2013) gave the empirical g.f. -x*(x-10) / ((x+1)*(x^2-11*x+1));
Sela Fried (Oct 14 2024) notes that a(n) = 10*a(n-1) + 10*a(n-2) - a(n-3) for n >= 4, from
which the conjectured g.f. follows.

Formalization: the g.f. of the offset-1 sequence is Sum_{n >= 1} a(n) x^n, written as
`PowerSeries.mk` of the function that is 0 at n = 0 and a(n) for n ≥ 1. The identity is
stated over ℤ⟦X⟧, cross-multiplied by the denominator (x+1)*(x^2-11*x+1), whose constant
coefficient is 1.
-/

namespace OMA.S_oeis_a138365

open PowerSeries

/-- A006190: b(0) = 0, b(1) = 1, b(n) = 3*b(n-1) + b(n-2). -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 3 * b (n + 1) + b n

/-- A138365: a(n) = A006190(n) * A006190(n+2) (offset 1). -/
def a (n : ℕ) : ℤ := b n * b (n + 2)

/-- Barker's empirical g.f., cross-multiplied by its denominator. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then 0 else a n) * ((X + 1) * (X ^ 2 - 11 * X + 1)) =
      -X * (X - 10) := by
  sorry

end OMA.S_oeis_a138365
