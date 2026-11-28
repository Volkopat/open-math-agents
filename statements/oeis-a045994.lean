import Mathlib

/-!
# OEIS A045994: Mathar's D-finite recurrence for a Motzkin convolution

Source: https://oeis.org/A045994 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane), offset 0: a(0)=1, a(n) = M(n) + Sum_{k=1..n-1} M(k)*a(n-k-1), where M(n)
are the Motzkin numbers (A001006). Data: 1, 1, 3, 7, 18, 47, 125, ... Formula: Conjecture:
(n+1)*a(n) + 2*(-2*n-1)*a(n-1) + 2*(-n+3)*a(n-2) + (11*n-19)*a(n-3) + (11*n-27)*a(n-4) +
3*(n-3)*a(n-5) = 0. - R. J. Mathar, Sep 27 2013

Formalization notes:
* `M` is the Motzkin sequence A001006 given by M(0) = M(1) = 1 and Bernhart's recurrence
  M(n+2) - M(n+1) = M(0) M(n) + M(1) M(n-1) + ... + M(n) M(0), listed in A001006 and used by the
  entry's Mathematica program (m[n] = m[n-1] + Sum[m[k] m[n-k-2], k = 0..n-2]).
* `a` is the entry's definition, written for the index n + 1: a(n+1) = M(n+1) +
  Sum_{k=1..n} M(k) a(n-k).
* `main` states the recurrence, in the integers, for every n >= 5: the range in which a(n), ...,
  a(n-5) are all terms of the sequence (offset 0), so every natural subtraction n - j is exact.
* Controls proved in the proof file: M(2..5) = 2, 4, 9, 21 and a(1..5) = 1, 3, 7, 18, 47 as in
  the entries' data.
-/

namespace OMA.S_oeis_a045994

/-- The Motzkin numbers A001006: M(0) = M(1) = 1 and
M(n+2) = M(n+1) + Sum_{k=0..n} M(k) M(n-k) (Bernhart's recurrence in A001006). -/
def M : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => M (n + 1) + ∑ k : Fin (n + 1), M k * M (n - k)

/-- A045994: a(0) = 1 and a(n) = M(n) + Sum_{k=1..n-1} M(k) a(n-k-1) for n >= 1, written for
the index n + 1. -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => M (n + 1) + ∑ k ∈ Finset.Icc 1 n, M k * a (n - k)

/-- Mathar's conjecture: the recurrence holds for every n >= 5. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 1) * a n + 2 * (-2 * (n : ℤ) - 1) * a (n - 1) + 2 * (-(n : ℤ) + 3) * a (n - 2) +
      (11 * (n : ℤ) - 19) * a (n - 3) + (11 * (n : ℤ) - 27) * a (n - 4) +
      3 * ((n : ℤ) - 3) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a045994
