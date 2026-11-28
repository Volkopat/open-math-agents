import Mathlib

/-!
# OEIS A177200: Mathar's D-finite recurrence for a convolution-defined sequence

Source: https://oeis.org/A177200 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Richard Choulet, May 04 2010), offset 0: Sequence defined by the recurrence formula
a(n+1)=sum(a(p)*a(n-p)+k,p=0..n)+l for n>=1, with here a(0)=1, a(1)=9, k=-1 and l=1. Example:
a(2)=2*1*9-2+1=17. a(3)=2*1*17-2+81-1+1=113. Data: 1, 9, 17, 113, 529, 3377, 20113, ... Formula:
Conjecture: +(n+1)*a(n) +(-7*n+2)*a(n-1) +(-17*n+43)*a(n-2) +3*(29*n-90)*a(n-3) +96*(-n+4)*a(n-4)
+32*(n-5)*a(n-5)=0. - R. J. Mathar, Mar 02 2016

Formalization notes:
* `a` is the entry's recurrence with k = -1 and l = 1: for n >= 1,
  a(n+1) = Sum_{p=0..n} (a(p) a(n-p) - 1) + 1. In Lean the index n + 1 >= 2 is written n + 2 and
  the sum runs over p in Fin (n + 2), that is p = 0..n+1.
* `main` states the recurrence, in the integers, for every n >= 5: the range in which a(n), ...,
  a(n-5) are all terms of the sequence (offset 0), so every natural subtraction n - j is exact.
* Controls proved in the proof file: a(0..5) = 1, 9, 17, 113, 529, 3377 as in the entry's data.
-/

namespace OMA.S_oeis_a177200

/-- A177200: a(0) = 1, a(1) = 9, and a(n+1) = Sum_{p=0..n} (a(p) a(n-p) - 1) + 1 for n >= 1
(the entry's recurrence with k = -1 and l = 1). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 9
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) - 1)) + 1

/-- Mathar's conjecture: the recurrence holds for every n >= 5. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 1) * a n + (-7 * (n : ℤ) + 2) * a (n - 1) + (-17 * (n : ℤ) + 43) * a (n - 2) +
      3 * (29 * (n : ℤ) - 90) * a (n - 3) + 96 * (-(n : ℤ) + 4) * a (n - 4) +
      32 * ((n : ℤ) - 5) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a177200
