import Mathlib

/-!
# OEIS A177126: Mathar's D-finite recurrence for a convolution-defined sequence

Source: https://oeis.org/A177126 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Richard Choulet, May 03 2010), offset 0: Sequence defined by the recurrence formula
a(n+1)=sum(a(p)*a(n-p)+k,p=0..n)+l for n>=1, with here a(0)=1, a(1)=10, k=1 and l=1. Data:
1, 10, 23, 150, 765, 5065, 32337, ... Formula: Conjecture: n*(n+1)*a(n) -n*(7*n-2)*a(n-1) -3*n*(7*n-17)*a(n-2) +n*(83*n-250)*a(n-3) -84*n*(n-4)*a(n-4) +28*n*(n-5)*a(n-5)=0. - R. J. Mathar, Jul 24 2012

Formalization notes:
* `a` is the entry's recurrence with k = 1 and l = 1: for n >= 1,
  a(n+1) = Sum_{p=0..n} (a(p) a(n-p) + k) + l. In Lean the index n + 1 >= 2 is written n + 2 and
  the sum runs over p in Fin (n + 2), that is p = 0..n+1.
* `main` states the recurrence, in the integers, for every n >= 5: the range in which a(n), ...,
  a(n-5) are all terms of the sequence (offset 0), so every natural subtraction n - j is exact.
* Controls proved in the proof file: a(0..5) = 1, 10, 23, 150, 765, 5065 as in the entry's data.
-/

namespace OMA.S_oeis_a177126

/-- A177126: a(0) = 1, a(1) = 10, and a(n+1) = Sum_{p=0..n} (a(p) a(n-p) + k) + l
for n >= 1 with k = 1 and l = 1 (the entry's recurrence). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 10
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) + 1)) + 1

/-- Mathar's conjecture: the recurrence holds for every n >= 5. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (n : ℤ) * ((n : ℤ) + 1) * a n +
      -(n : ℤ) * (7 * (n : ℤ) - 2) * a (n - 1) +
      -3 * (n : ℤ) * (7 * (n : ℤ) - 17) * a (n - 2) +
      (n : ℤ) * (83 * (n : ℤ) - 250) * a (n - 3) +
      -84 * (n : ℤ) * ((n : ℤ) - 4) * a (n - 4) +
      28 * (n : ℤ) * ((n : ℤ) - 5) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a177126
