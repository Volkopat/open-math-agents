import Mathlib

/-!
# Mathar's recurrence for OEIS A103138

A103138 is the second column of the inverse of the Delannoy triangle. Its entry gives the g.f.
(1 - x S(-x)) x S(-x), where S(x) is the g.f. of the large Schröder numbers A006318, and
A006318(n) = Sum_{k=0..n} A000108(k) binomial(n+k, n-k) (A000108 = Catalan numbers). Offset 0.
R. J. Mathar conjectured on December 14, 2011 that
2n a(n) + (13n-20) a(n-1) + (8n-27) a(n-2) + (n-5) a(n-3) = 0.
The entry does not give a range; it is stated here for n ≥ 3, where every index is at least 0.

Source: https://oeis.org/A103138
Credit: @jes5199
-/

namespace OMA.S_oeis_a103138

open PowerSeries

/-- The large Schröder numbers A006318. -/
def schroeder (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), catalan k * (n + k).choose (n - k)

/-- S(-x), where S is the g.f. of A006318. -/
noncomputable def sNeg : PowerSeries ℤ := mk fun n => (-1) ^ n * (schroeder n : ℤ)

noncomputable def gf : PowerSeries ℤ := (1 - X * sNeg) * (X * sNeg)

noncomputable def a (n : ℕ) : ℤ := coeff n gf

theorem main : ∀ n : ℕ, 3 ≤ n →
    2 * (n : ℤ) * a n + (13 * n - 20 : ℤ) * a (n - 1) + (8 * n - 27 : ℤ) * a (n - 2) +
      ((n : ℤ) - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a103138
