import Mathlib

/-!
# A097204: Mathar's recurrence for the binomial transform of n! - 1

Source: https://oeis.org/A097204
Credit: @ivillar

A033312(n) = n! - 1. A097204 (offset 0) is its binomial transform,
a(n) = Sum_{k=0..n} C(n,k)*(k! - 1); data 0, 0, 1, 8, 49, 294, 1893, 13572, 109345, ...

Conjecture (R. J. Mathar, Nov 16 2012):
a(n) + (-n-5)*a(n-1) + (5*n+3)*a(n-2) + 4*(-2*n+3)*a(n-3) + 4*(n-3)*a(n-4) = 0.

Formalization: the terms are integers, and the recurrence is stated for every n ≥ 4, the range in
which a(n-4) is defined.
-/

namespace OMA.S_oeis_a097204

/-- a(n) = ∑_{k=0}^{n} C(n,k) (k! - 1), the binomial transform of A033312. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * ((k.factorial : ℤ) - 1)

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    a n + (-(n : ℤ) - 5) * a (n - 1) + (5 * (n : ℤ) + 3) * a (n - 2) +
      4 * (-2 * (n : ℤ) + 3) * a (n - 3) + 4 * ((n : ℤ) - 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a097204
