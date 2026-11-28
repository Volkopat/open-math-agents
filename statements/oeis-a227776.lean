import Mathlib

/-!
# A227776: a(n) = 6*n^2 + 1.

Source: https://oeis.org/A227776
Credit: @agchua

Comment line of A227776 (Clark Kimberling, Jul 30 2013), verbatim:
  Least splitter is defined for x < y at A227631 as the least positive integer d such that
  x <= c/d < y for some integer c; the number c/d is called the least splitting rational of x
  and y.  Conjecture:  a(n) is the least splitter of s(n) and s(n+1), where s(n) = n*sin(1/n).
The offset of A227776 is 0, but s(0) = 0*sin(1/0) is undefined, so the conjecture has content
for n >= 1 and is stated for n >= 1. The statement also records s(n) < s(n+1), which the
definition of the least splitter presupposes. The least splitter of x and y is the least
element (IsLeast) of the set of splitters d of x and y.
-/

namespace OMA.S_oeis_a227776

/-- A227776: a(n) = 6*n^2 + 1. -/
def a (n : ℕ) : ℕ := 6 * n ^ 2 + 1

/-- s(n) = n*sin(1/n). -/
noncomputable def s (n : ℕ) : ℝ := (n : ℝ) * Real.sin (1 / (n : ℝ))

/-- d is a splitter of x and y: a positive integer with x <= c/d < y for some integer c. -/
def IsSplitter (x y : ℝ) (d : ℕ) : Prop :=
  0 < d ∧ ∃ c : ℤ, x ≤ (c : ℝ) / (d : ℝ) ∧ (c : ℝ) / (d : ℝ) < y

/-- For n >= 1, a(n) is the least splitter of s(n) and s(n+1). -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    s n < s (n + 1) ∧ IsLeast {d : ℕ | IsSplitter (s n) (s (n + 1)) d} (a n) := by
  sorry

end OMA.S_oeis_a227776
