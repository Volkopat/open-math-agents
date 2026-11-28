import Mathlib

/-!
# A189786: a(n) = n + [nr/t] + [ns/t]; r=Pi/2, s=arcsin(5/13), t=arcsin(12/13).

Source: https://oeis.org/A189786
Credit: @agchua

Comment of A189786 (Harvey P. Dale, Dec 07 2018):
  Conjecture: Sequence consists of all the positive even numbers except numbers of the form
  8*x+6, x >= 0.
Offset of A189786: 1 (data 2, 4, 8, 10, 12, 16, 18, 20, ...).

Formalisation. [x] is the floor function, as in the entry's Mathematica program
(n + Floor[(n*Pi/2)/t] + Floor[(n*ArcSin[5/13])/t] with t = ArcSin[12/13]); a(n) is an integer.
The conjecture says that the set of the values a(n), n >= 1, is exactly the set of the positive
even integers that are not of the form 8*x+6 with x >= 0.
-/

namespace OMA.S_oeis_a189786

/-- a(n) = n + floor(n*r/t) + floor(n*s/t) with r = Pi/2, s = arcsin(5/13), t = arcsin(12/13). -/
noncomputable def a (n : ℕ) : ℤ :=
  (n : ℤ) + ⌊(n : ℝ) * (Real.pi / 2) / Real.arcsin (12 / 13)⌋ +
    ⌊(n : ℝ) * Real.arcsin (5 / 13) / Real.arcsin (12 / 13)⌋

/-- The conjecture: the values a(n), n >= 1, are exactly the positive even numbers except the
numbers of the form 8*x+6, x >= 0. -/
theorem main : ∀ m : ℤ, (∃ n : ℕ, 1 ≤ n ∧ a n = m) ↔
    (0 < m ∧ Even m ∧ ¬ ∃ x : ℕ, m = 8 * (x : ℤ) + 6) := by
  sorry

end OMA.S_oeis_a189786
