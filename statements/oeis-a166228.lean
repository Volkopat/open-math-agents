import Mathlib

/-!
# A166228: Alternating sum of large Schroeder numbers

Source: https://oeis.org/A166228 (conjecture by R. J. Mathar, Nov 17 2011)

`a(n)` (offset 0) is `Sum_{k=0..n} (-1)^(n-k)*A006318(k)`, the alternating sum of the large
Schroeder numbers A006318 (Mathlib's `largeSchroder`).

The conjecture, stated for `n >= 3` (where every index is defined):
Conjecture: (n+1)*a(n) +(4-5n)*a(n-1) +(1-5n)*a(n-2) +(n-2)*a(n-3)=0.
-/

namespace OMA.S_oeis_a166228

open PowerSeries

/-- The alternating sum of the large Schroeder numbers. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (-1) ^ (n - k) * (Nat.largeSchroder k : ℤ)

theorem main : ∀ n : ℕ, 3 ≤ n →
      ((n : ℤ) + 1) * a n + (4 - 5 * (n : ℤ)) * a (n - 1) + (1 - 5 * (n : ℤ)) * a (n - 2) +
        ((n : ℤ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a166228
