import Mathlib

/-!
# A337500: a(n) is the number of ballot sequences of length n tied or won by at most 3 votes.

Source: https://oeis.org/A337500
Credit: @agchua

R. J. Mathar (Sep 27 2020), in the formula section of A337500, verbatim:
  Conjecture: D-finite with recurrence -(n+3)*(n-4)*a(n) +2*(n^2-2*n-11)*a(n-1) +4*(n-1)^2*a(n-2)
  -8*(n-1)*(n-2)*a(n-3)=0.
Offset 0. Definition: a sequence of n votes for two candidates with k votes for the first one ends
with margin |n - 2k|, and there are binomial(n,k) such sequences, so a(n) is the sum of
binomial(n,k) over the k in 0..n with |n - 2k| <= 3, written below without subtraction as
n <= 2k+3 and 2k <= n+3 (the same count as the entry's comments: n-step walks on the path graph
of the integers ending within 3 steps of the origin; it reproduces all 31 listed terms). The
recurrence is stated over the integers for every n >= 3, the range in which all four indices are
terms.
-/

namespace OMA.S_oeis_a337500

/-- A337500: the number of words of length n over two letters whose letter counts differ by at
most 3, as a sum of binomial coefficients. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if n ≤ 2 * k + 3 ∧ 2 * k ≤ n + 3 then n.choose k else 0

/-- Mathar's conjectured recurrence, for every n >= 3. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    -((n : ℤ) + 3) * ((n : ℤ) - 4) * a n + 2 * ((n : ℤ) ^ 2 - 2 * n - 11) * a (n - 1)
      + 4 * ((n : ℤ) - 1) ^ 2 * a (n - 2) - 8 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a337500
