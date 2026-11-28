import Mathlib

/-!
# A053482: Mathar's recurrence for the binomial transform of A029767

Source: https://oeis.org/A053482
Credit: @ivillar

Status: known result. The entry records the formula a(n) = 3*n*a(n-2)-2*n*(n-1)*a(n-2)+1, derived from the
array T(n,k) of its comments, with the remark that it proves the conjecture (Richard Choulet,
Dec 17 2012).

A029767(n) = (n-1)!*(2^n - 1) for n ≥ 1 (1, 3, 14, 90, 744, ...). A053482 (offset 0) is its
binomial transform, taken from the first positive index: by the formula in the entry,
a(n) = Sum_{k=0..n} C(n,k)*k!*(2^(k+1) - 1) = Sum_{k=0..n} C(n,k)*A029767(k+1);
data 1, 4, 21, 142, 1201, 12336, 149989, ...

Conjecture (R. J. Mathar, Sep 29 2012):
a(n) - (3*n+1)*a(n-1) + (2*n+3)*(n-1)*a(n-2) - 2*(n-1)*(n-2)*a(n-3) = 0.

Formalization: the terms are integers, and the recurrence is stated for every n ≥ 3, the range in
which a(n-3) is defined.
-/

namespace OMA.S_oeis_a053482

/-- a(n) = ∑_{k=0}^{n} C(n,k) k! (2^(k+1) - 1). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * (k.factorial : ℤ) * (2 ^ (k + 1) - 1)

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    a n - (3 * (n : ℤ) + 1) * a (n - 1) + (2 * (n : ℤ) + 3) * ((n : ℤ) - 1) * a (n - 2) -
      2 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a053482
