import Mathlib

/-!
# A138830: Bisection of imperfect numbers A132999.

Source: https://oeis.org/A138830 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry A138830 (Omar E. Pol, Apr 06 2008), offset 1, data 2, 4, 7, 9, 11, 13, ..., 27, 30, 32, ...
Comment, verbatim:
The conjectured g.f. (-x^14+x^13-x^3+x^2+2)/(x^2-2*x+1) that a correspondent suggested is wrong
and fails after roughly 240 terms [R. J. Mathar, Jun 15 2009]

Formalization notes:
* A132999 (offset 1) lists the imperfect numbers, the positive integers not equal to the sum of
  their proper divisors, in increasing order: A132999(k) = `Nat.nth isImperfect (k - 1)`.
* "Bisection": A138830(n) = A132999(2n) for n >= 1, which reproduces the entry's data
  (A132999 = 1, 2, 3, 4, 5, 7, 8, 9, ..., so A132999(2), A132999(4), A132999(6) = 2, 4, 7).
* The suggested g.f. has constant term 2 = A138830(1), so it is read with the entry's first term
  as the coefficient of x^0: the power series is A = Sum_{k >= 0} A138830(k+1) x^k over the
  rationals (with the other reading, Sum_{n >= 1} A138830(n) x^n, the g.f. would already fail at
  x^0). The suggested g.f. is G = N * D⁻¹ with N = -x^14+x^13-x^3+x^2+2 and D = x^2-2x+1, whose
  constant term is 1.
* The claim is stated as: G agrees with A on the first 240 terms (the coefficients of x^0, ...,
  x^239), which is how far the suggestion was matched ("fails after roughly 240 terms"), and
  G is not equal to A ("is wrong").
-/

namespace OMA.S_oeis_a138830

open PowerSeries

/-- An imperfect number: a positive integer not equal to the sum of its proper divisors. -/
def isImperfect (n : ℕ) : Prop := 0 < n ∧ ∑ d ∈ n.properDivisors, d ≠ n

/-- A132999(k), the k-th imperfect number (offset 1). -/
noncomputable def A132999 (k : ℕ) : ℕ := Nat.nth isImperfect (k - 1)

/-- A138830(n) = A132999(2n), the bisection of A132999 (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := A132999 (2 * n)

/-- The power series Sum_{k >= 0} A138830(k+1) x^k. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun k => (a (k + 1) : ℚ)

/-- The suggested generating function (-x^14+x^13-x^3+x^2+2)/(x^2-2*x+1). -/
noncomputable def G : ℚ⟦X⟧ :=
  (-X ^ 14 + X ^ 13 - X ^ 3 + X ^ 2 + 2) * (X ^ 2 - 2 * X + 1)⁻¹

/-- Mathar's remark in OEIS A138830: the suggested g.f. matches the first 240 terms but is
wrong. -/
theorem main : (∀ k < 240, coeff k A = coeff k G) ∧ A ≠ G := by
  sorry

end OMA.S_oeis_a138830
