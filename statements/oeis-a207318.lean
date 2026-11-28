import Mathlib

/-!
# A207318: alternating partial sums of the Franel numbers
Source: https://oeis.org/A207318 (R. J. Mathar, Nov 28 2013)

a(n) = Sum_{k=0..n-1} (-1)^k * A000172(k) (offset 0), where A000172(k) = Sum_{j=0..k} binomial(k,j)^3
are the Franel numbers.

Conjecture: (n-1)^2*a(n) + (2*n-3)*(3*n-5)*a(n-1) + (-15*n^2+53*n-48)*a(n-2) + 8*(n-2)^2*a(n-3) = 0,
for every n for which all terms are defined, i.e. n >= 3.
-/

namespace OMA.S_oeis_a207318

/-- Franel numbers A000172. -/
def franel (k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), (k.choose j) ^ 3

/-- A207318. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, (-1) ^ k * (franel k : ℤ)

theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) - 1) ^ 2 * a n + (2 * (n : ℤ) - 3) * (3 * (n : ℤ) - 5) * a (n - 1)
      + (-15 * (n : ℤ) ^ 2 + 53 * (n : ℤ) - 48) * a (n - 2) + 8 * ((n : ℤ) - 2) ^ 2 * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a207318
