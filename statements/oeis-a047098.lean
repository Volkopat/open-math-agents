import Mathlib

/-!
# A047098: a(n) = 2*binomial(3*n, n) - Sum_{k=0..n} binomial(3*n, k)
Source: https://oeis.org/A047098 (R. J. Mathar, Nov 30 2012)

The sequence is defined by its title (offset 0):
a(n) = 2*binomial(3n, n) - Sum_{k=0..n} binomial(3n, k).

Conjecture: 2*n*(2*n-1)*a(n) + (-71*n^2+112*n-48)*a(n-1) + 3*(131*n^2-391*n+296)*a(n-2)
- 72*(3*n-7)*(3*n-8)*a(n-3) = 0, for every n for which all terms are defined, i.e. n >= 3.
-/

namespace OMA.S_oeis_a047098

/-- A047098. -/
def a (n : ℕ) : ℤ :=
  2 * ((3 * n).choose n : ℤ) - ∑ k ∈ Finset.range (n + 1), ((3 * n).choose k : ℤ)

theorem main : ∀ n : ℕ, 3 ≤ n →
    2 * (n : ℤ) * (2 * (n : ℤ) - 1) * a n + (-71 * (n : ℤ) ^ 2 + 112 * (n : ℤ) - 48) * a (n - 1)
      + 3 * (131 * (n : ℤ) ^ 2 - 391 * (n : ℤ) + 296) * a (n - 2)
      - 72 * (3 * (n : ℤ) - 7) * (3 * (n : ℤ) - 8) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a047098
