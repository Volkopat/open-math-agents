import Mathlib

/-!
# A135051: Pyramid game person numbers that have integer solutions.

Source: https://oeis.org/A135051
Credit: @agchua

Colin Barker (Apr 30 2012), in the formula section of A135051, verbatim:
  From _Colin Barker_, Apr 30 2012: (Start)
  Conjecture: a(n) = 9 - 2*(-1)^n + 4*(-8+(-1)^n)*n + 32*n^2.
  Conjecture: G.f.: x*(7 + 72*x + 98*x^2 + 72*x^3 + 7*x^4)/((1-x)^3*(1+x)^2). (End)
Offset 1. Definition, from the entry's comment and its Mathematica program: the terms are the
numbers n ≥ 1 such that 2*sqrt(8n - 7) is an integer and n ≡ 7 (mod 8), in increasing order.
For n ≥ 1, 2*sqrt(8n - 7) is an integer iff 4(8n - 7) = k^2 for a natural number k; every n
with n ≡ 7 (mod 8) is at least 7, so the natural-number subtraction 8n - 7 below is exact.
a(n) is the (n-1)-th (counting from 0) number with this property, and a(0) = 0, in accordance
with the factor x of the g.f. (offset 1). This file states both conjectures: the closed form
for all n ≥ 1, and the g.f. as an identity of formal power series over ℚ,
(∑ a(n) X^n) * ((1 - X)^3 (1 + X)^2) = X * (7 + 72X + 98X^2 + 72X^3 + 7X^4).
-/

namespace OMA.S_oeis_a135051

/-- The defining property: 2*sqrt(8n - 7) is an integer (i.e. 4(8n - 7) is a square) and
n ≡ 7 (mod 8). -/
def IsTerm (n : ℕ) : Prop := (∃ k : ℕ, k ^ 2 = 4 * (8 * n - 7)) ∧ n % 8 = 7

/-- A135051(n) for n ≥ 1: the n-th number with the property IsTerm; a(0) = 0. -/
noncomputable def a (n : ℕ) : ℕ := if n = 0 then 0 else Nat.nth IsTerm (n - 1)

/-- Colin Barker's conjectures: a(n) = 9 - 2(-1)^n + 4(-8 + (-1)^n)n + 32n^2 for n ≥ 1, and the
g.f. x(7 + 72x + 98x^2 + 72x^3 + 7x^4)/((1-x)^3 (1+x)^2). -/
theorem main : (∀ n : ℕ, 1 ≤ n →
      (a n : ℤ) = 9 - 2 * (-1) ^ n + 4 * (-8 + (-1) ^ n) * n + 32 * n ^ 2) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2) =
      PowerSeries.X * (7 + 72 * PowerSeries.X + 98 * PowerSeries.X ^ 2 +
        72 * PowerSeries.X ^ 3 + 7 * PowerSeries.X ^ 4) := by
  sorry

end OMA.S_oeis_a135051
