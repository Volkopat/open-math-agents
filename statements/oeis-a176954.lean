import Mathlib

/-!
# OEIS A176954: Mathar's D-finite recurrence for a convolution-defined sequence

Source: https://oeis.org/A176954 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Richard Choulet, Apr 29 2010), offset 0: a(n+1) = 1 + Sum_{p=0..n} a(p)*a(n-p)+k for n>=1, with here a(0)=1, a(1)=2, k=-1 and l=-1. Data:
1, 2, 1, 2, 3, 9, 27, ... Formula: Conjecture: (n+1)*a(n) +(2-7n)*a(n-1) +(11n-13)*a(n-2) + (11n-46)*a(n-3) +4*(29-7n)*a(n-4) +12(n-5)*a(n-5)=0. - R. J. Mathar, Nov 21 2011

Entry's program and example: (Maple) l:=-1: k:=-1: m:=2: d(0):=1: d(1):=m: for n from 1 to 30 do
d(n+1):=sum(d(p)*d(n-p)+k, p=0..n)+l: od; a(2)=2*1*2-2-1=1. a(3)=2*1*1-2+2^2-1-1=2.

Formalization notes:
* The name as printed drops the parentheses and the l of its family (A176953, A177180, ...): read
  literally, a(n+1) = 1 + Sum a(p) a(n-p) + k gives a(2) = 4, against the data. The entry's Maple
  program, its example and its data all follow a(n+1) = Sum_{p=0..n} (a(p) a(n-p) + k) + l with
  k = -1 and l = -1, and `a` is that recurrence. In Lean the index n + 1 >= 2 is written n + 2 and
  the sum runs over p in Fin (n + 2), that is p = 0..n+1.
* `main` states the recurrence, in the integers, for every n >= 5: the range in which a(n), ...,
  a(n-5) are all terms of the sequence (offset 0), so every natural subtraction n - j is exact.
* Controls proved in the proof file: a(0..5) = 1, 2, 1, 2, 3, 9 as in the entry's data.
-/

namespace OMA.S_oeis_a176954

/-- A176954: a(0) = 1, a(1) = 2, and a(n+1) = Sum_{p=0..n} (a(p) a(n-p) + k) + l
for n >= 1 with k = -1 and l = -1 (the entry's recurrence). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) - 1)) - 1

/-- Mathar's conjecture: the recurrence holds for every n >= 5. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 1) * a n +
      (2 - 7 * (n : ℤ)) * a (n - 1) +
      (11 * (n : ℤ) - 13) * a (n - 2) +
      (11 * (n : ℤ) - 46) * a (n - 3) +
      4 * (29 - 7 * (n : ℤ)) * a (n - 4) +
      12 * ((n : ℤ) - 5) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a176954
