import Mathlib

/-!
# A recurrence for a binomial sum

R. J. Mathar's conjecture of November 2, 2026, in OEIS A386829, for the
integer sequence defined by Seiichi Manyama's original finite sum.
-/
namespace OMA.S_oeis_a386829

def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n+1), 3^k * 2^(n-k) * (2*n+1).choose k * (2*n-k).choose (n-k)

theorem main : ∀ n : ℕ, 2 ≤ n →
    2*(n:ℤ)*(a n:ℤ) + (-31*(n:ℤ)+20)*(a (n-1):ℤ) +
    90*(-2*(n:ℤ)+1)*(a (n-2):ℤ) = 0 := by
  sorry

end OMA.S_oeis_a386829
