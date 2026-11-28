import Mathlib

/-!
# OEIS A131439, the inverse binomial transform of A131438

Source: https://oeis.org/A131439 and https://oeis.org/A131438
Credit: @etaubman

The OEIS specifies zero offset when applying the transform. The input at k
therefore uses A131438 at its original index k+1. The signed binomial sum is
over the integers.
-/

namespace OMA.S_oeis_a131439

def input (k : ℕ) : ℤ := ((k : ℤ) + 3) * 2 ^ (k + 1) - 3 * k - 5

def sequence (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * input k

theorem main : sequence 0 = 1 ∧ sequence 1 = 7 ∧
    ∀ k : ℕ, sequence (k + 2) = 4 * (k : ℤ) + 14 := by
  sorry

end OMA.S_oeis_a131439
