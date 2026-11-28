import Mathlib

/-!
# Prime counts between consecutive factorials (OEIS A061232)

The index zero corresponds to the interval (0!, 1!]. The ratio uses the
indices printed in Mohammed Bouayoun's 2006 conjecture.
-/

namespace OMA.S_oeis_a061232

def a (n : ℕ) : ℕ :=
  Nat.primeCounting (n+1).factorial - Nat.primeCounting n.factorial

theorem main : ∀ n : ℕ, 2 < n →
    (n : ℚ) + 1/2 ≤ (a n : ℚ) / a (n-1) ∧
    (a n : ℚ) / a (n-1) ≤ n + 2/3 := by
  sorry

end OMA.S_oeis_a061232
