import Mathlib

/-!
# A325696: length-3 strict compositions of n such that no part is the sum of the other two

Source: https://oeis.org/A325696
Credit: @xor2k
Sibling of OEIS A325695 (same conjecture wording); statement modelled on the accepted one for that entry.

OEIS (offset 0): Number of length-3 strict compositions of n such that no part is the sum of
the other two. A composition of n is a finite sequence of positive integers summing to n. It is
strict if all parts are distinct. Conjectures from Colin Barker, May 16 2019:
G.f.: 6*x^7*(1 + x + 2*x^2) / ((1 - x)^3*(1 + x)^2*(1 + x^2)*(1 + x + x^2)).
a(n) = a(n-2) + a(n-3) + a(n-4) - a(n-5) - a(n-6) - a(n-7) + a(n-9) for n>9.

Conventions: a length-3 strict composition of n is an ordered triple (a, b, c) of pairwise
distinct positive integers with a + b + c = n. The first two parts a, b (each at most n) are
the free coordinates and the third part is obtained by subtracting a + b from n (the equation
a + b + c = n rules out truncation). Every valid composition occurs exactly once. The
recurrence is stated for n = k + 10, all k >= 0, with the negative terms moved across. The
rational generating function is stated with the denominator multiplied across; since the
denominator has constant coefficient 1, this specifies the ordinary generating function
uniquely.
-/

namespace OMA.S_oeis_a325696

/-- The composition `(a, b, n - (a + b))` is strict and no part is the sum of the other two. -/
def allowed (n a b : ℕ) : Bool :=
  let c := n-(a+b)
  decide (0<a ∧ 0<b ∧ 0<c ∧ a+b+c=n ∧ a≠b ∧ a≠c ∧ b≠c ∧ a≠b+c ∧ b≠a+c ∧ c≠a+b)

/-- A325696(n). -/
def term (n : ℕ) : ℕ := ∑ a ∈ Finset.range (n+1),
  ((Finset.range (n+1)).filter (fun b => allowed n a b)).card

noncomputable def series : PowerSeries ℚ := PowerSeries.mk (fun n => term n)

open PowerSeries in
/-- Barker's recurrence (for n > 9) and generating function. -/
theorem main :
    (∀ k : ℕ, term (k+10)+term (k+5)+term (k+4)+term (k+3) =
      term (k+8)+term (k+7)+term (k+6)+term (k+1)) ∧
    ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2))*series = 6*X^7*(1+X+2*X^2) := by
  sorry

end OMA.S_oeis_a325696
