import Mathlib

/-!
# A207323: weighted partial sums of A002893
Source: https://oeis.org/A207323 (R. J. Mathar, Nov 28 2013)

a(n) = Sum_{k=0..n} k * A002893(k) (offset 0), where A002893(k) = Sum_{j=0..k} binomial(k,j)^2 * binomial(2j,j).

Conjecture: n*(n-1)*a(n) + (-14*n^2+23*n-12)*a(n-1) + (52*n^2-151*n+120)*a(n-2)
  + 3*(-22*n^2+79*n-72)*a(n-3) + 27*(n-2)^2*a(n-4) = 0,
for every n for which all terms are defined, i.e. n >= 4.
-/

namespace OMA.S_oeis_a207323

/-- A002893. -/
def A002893 (k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), (k.choose j) ^ 2 * (2 * j).choose j

/-- A207323. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (k : ℤ) * (A002893 k : ℤ)

theorem main : ∀ n : ℕ, 4 ≤ n →
    (n : ℤ) * ((n : ℤ) - 1) * a n + (-14 * (n : ℤ) ^ 2 + 23 * (n : ℤ) - 12) * a (n - 1)
      + (52 * (n : ℤ) ^ 2 - 151 * (n : ℤ) + 120) * a (n - 2)
      + 3 * (-22 * (n : ℤ) ^ 2 + 79 * (n : ℤ) - 72) * a (n - 3)
      + 27 * ((n : ℤ) - 2) ^ 2 * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a207323
