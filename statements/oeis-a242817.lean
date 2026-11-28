import Mathlib

/-!
# A242817: Dobinski's formula for the Bell polynomial values B(n,n)

Source: https://oeis.org/A242817
Credit: @ivillar

Status: known result: the entry notes that this is the case x = n of the Dobinski-type formula for B(n,x) (Pontus von Brömssen, Dec 05 2020).

A242817 (offset 0): a(n) = B(n,n), where B(n,x) = Sum_{k=0..n} Stirling2(n,k)*x^k are the Bell
polynomials (also known as exponential or Touchard polynomials);
data 1, 1, 6, 57, 756, 12880, 268098, ...

Conjecture (Nicolas Nagel, Apr 20 2016): the equation a(n)*e^n = Sum_{k>=0} k^n*n^k/k! is true
for every positive integer n. Pontus von Brömssen (Dec 05 2020) notes in the entry that this is
the special case x = n of the formula B(n,x) = e^(-x) * Sum_{k>=0} k^n*x^k/k!.

Formalization: `Nat.stirlingSecond n k` is Mathlib's Stirling number of the second kind. The
infinite sum is the sum of the (absolutely convergent) real series, written with `tsum`.
-/

namespace OMA.S_oeis_a242817

/-- a(n) = B(n,n) = ∑_{k=0}^{n} Stirling2(n,k) n^k. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k * n ^ k

/-- Nagel's conjecture: a(n) e^n = ∑_{k ≥ 0} k^n n^k / k!. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℝ) * Real.exp n = ∑' k : ℕ, (k : ℝ) ^ n * (n : ℝ) ^ k / (k.factorial : ℝ) := by
  sorry

end OMA.S_oeis_a242817
