import Mathlib

/-!
# A207319: a(n) = Sum_{k=0..n-1} (-1)^k*k*A000172(k)
Source: https://oeis.org/A207319 (R. J. Mathar, Nov 28 2013)

a(n) = Sum_{k=0..n-1} (-1)^k * k * A000172(k) (offset 0), where A000172(k) = Sum_{j=0..k} binomial(k,j)^3
are the Franel numbers.

Conjecture: (n-1)*(n-2)*a(n) + 2*(n^2+3*n-9)*a(n-1) + 3*(-13*n^2+63*n-80)*a(n-2)
+ 4*(17*n^2-96*n+136)*a(n-3) - 32*(n-3)^2*a(n-4) = 0,
for every n for which all terms are defined, i.e. n >= 4.
-/

namespace OMA.S_oeis_a207319

/-- Franel numbers A000172. -/
def franel (k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), (k.choose j) ^ 3

/-- A207319. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, (-1) ^ k * (k : ℤ) * (franel k : ℤ)

theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) - 1) * ((n : ℤ) - 2) * a n + 2 * ((n : ℤ) ^ 2 + 3 * (n : ℤ) - 9) * a (n - 1)
      + 3 * (-13 * (n : ℤ) ^ 2 + 63 * (n : ℤ) - 80) * a (n - 2)
      + 4 * (17 * (n : ℤ) ^ 2 - 96 * (n : ℤ) + 136) * a (n - 3) - 32 * ((n : ℤ) - 3) ^ 2 * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a207319
