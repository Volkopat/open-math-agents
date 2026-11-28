import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# OEIS A188486 and Kravitz's conjecture on odd square abundance

Source: https://oeis.org/A188486 (OEIS Foundation, CC BY-SA 4.0).
Credit: @anmolspace.

Sidney Kravitz conjectured that no positive integer has abundance equal to a positive
odd square. Eric W. Weisstein's OEIS entry lists known counterexamples.
-/

namespace OMA.S_oeis_a188486

-- Moving 2n to the right expresses the signed abundance condition without subtraction.
theorem main : ∀ n : ℕ, 0 < n → ∀ u : ℕ, 0 < u → Odd u →
    ArithmeticFunction.sigma 1 n ≠ 2 * n + u ^ 2 := by
  sorry

end OMA.S_oeis_a188486
