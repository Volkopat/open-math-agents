import Mathlib

/-!
# A138808: Number of integer pairs (x,y), x > 0, y > 0, such that x <= p, y <= q for any factorization n = p*q.

Source: https://oeis.org/A138808
Credit: @agchua

Comment of A138808 (R. J. Mathar, Aug 06 2008; the entry is by Jonas Wallgren, May 16 2008):
  Conjecture: the row sums of the plane partitions A010766 are upper bounds.
The sequence has offset 1. As the example for a(8) in the entry shows, a(n) counts the pairs of
positive integers (x, y) with x <= p and y <= q for at least one factorization n = p*q, that
is, the points of the union of the rectangles [1, p] x [1, n/p] over the divisors p of n; such
pairs have x, y <= n. A010766 is the triangle T(n, k) = floor(n/k), 1 <= k <= n, so its n-th row
sum is Sum_{k=1..n} floor(n/k). The conjecture says a(n) <= Sum_{k=1..n} floor(n/k) for n >= 1.
-/

namespace OMA.S_oeis_a138808

/-- A138808(n): the number of pairs (x, y) of positive integers with x <= p and y <= n/p for
some divisor p of n. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun xy : ℕ × ℕ => ∃ p ∈ Nat.divisors n, xy.1 ≤ p ∧ xy.2 ≤ n / p)).card

/-- The conjecture: the n-th row sum of A010766, Sum_{k=1..n} floor(n/k), is an upper bound
for a(n). -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≤ ∑ k ∈ Finset.Icc 1 n, n / k := by
  sorry

end OMA.S_oeis_a138808
