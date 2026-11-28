import Mathlib

/-!
# OEIS A189457: with r = 2, s = sqrt 2, t = 1 + sqrt 2 the rank sequence c is A186222

Source: https://oeis.org/A189457 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Apr 22 2011), offset 1: a(n) = n+[ns/r]+[nt/r]; r=2, s=sqrt(2),
t=1+sqrt(2). This is one of three sequences that partition the positive integers. In general,
suppose that r, s, t are positive real numbers for which the sets {i/r: i>=1}, {j/s: j>=1},
{k/t: k>=1} are pairwise disjoint. Let a(n) be the rank of n/r when all the numbers in the three
sets are jointly ranked. Define b(n) and c(n) as the ranks of n/s and n/t. It is easy to prove
that a(n) = n + [ns/r] + [nt/r], b(n) = n + [nr/s] + [nt/s], c(n) = n + [nr/t] + [ns/t], where
[]=floor. With r=2, s=sqrt(2), t=1+sqrt(2), a=A189457, b=A189458, c=A186222 (conjectured).
A186222 (Clark Kimberling), offset 1: Adjusted joint rank sequence of (g(i)) and (f(j)) with f(i)
after g(j) when f(i)=g(j), where f and g are the triangular numbers and squares. Complement of
A186221. Data: 1, 4, 6, 9, 11, 13, 16, 18, 21, 23, 26, 28, ...
The example in A186221 writes the triangular numbers 1, 3, 6, 10, ... and the squares 1, 4, 9, 16,
... and replaces each number by its rank, where ties are settled by ranking the triangular number
after the square; the squares get the ranks 1, 4, 6, 9, 11, 13, 16, 18, ...

Formalization notes:
* `c n` is c(n) = n + [nr/t] + [ns/t] with r = 2, s = sqrt 2, t = 1 + sqrt 2; both floors are of
  nonnegative numbers, so `Nat.floor` is the floor.
* `A186222 n` is the rank of the square n^2: the n squares 1, 4, ..., n^2 come at or before it, and
  so do the triangular numbers i(i+1)/2 (i >= 1) below n^2, while a triangular number equal to n^2
  is ranked after it.
* `main` states the conjectured identification c = A186222 for every n >= 1.
-/

namespace OMA.S_oeis_a189457

/-- c(n) = n + [nr/t] + [ns/t] with r = 2, s = sqrt 2, t = 1 + sqrt 2. -/
noncomputable def c (n : ℕ) : ℕ :=
  n + ⌊(n : ℝ) * 2 / (1 + Real.sqrt 2)⌋₊ + ⌊(n : ℝ) * Real.sqrt 2 / (1 + Real.sqrt 2)⌋₊

/-- A186222(n): the rank of n^2 when the squares and the triangular numbers are ranked together,
a triangular number equal to a square coming after it. -/
noncomputable def A186222 (n : ℕ) : ℕ :=
  n + Set.ncard {i : ℕ | 1 ≤ i ∧ i * (i + 1) / 2 < n ^ 2}

/-- The conjecture: c = A186222. -/
theorem main : ∀ n : ℕ, 1 ≤ n → c n = A186222 n := by
  sorry

end OMA.S_oeis_a189457
