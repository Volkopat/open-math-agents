import Mathlib

/-!
# A401046: Squares that are sums of two primes differing by 6

Source: https://oeis.org/A401046
Credit: @gblacher2
-/

namespace OMA.S_oeis_a401046

/-- The set of squares that are sums of two primes differing by 6 is infinite. -/
theorem main :
    {n : ℕ | ∃ k p : ℕ, n = k ^ 2 ∧ n = p + (p + 6) ∧ p.Prime ∧ (p + 6).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a401046
