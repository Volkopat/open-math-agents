import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc


/-!
# OEIS A181411: asymptotic growth of a binomial sum of divisor sums

Source: https://oeis.org/A181411 (OEIS Foundation, CC BY-SA 4.0).
Credit: @rkka02

Václav Kotesovec's conjecture is that `a(n) ~ (π²/4) * n * 2^n`, where
`a(n) = ∑_{k=0}^n binomial(n,k) * σ(n+k)` for `n ≥ 1`.
The finite sum also defines `a 0` for convenience in Lean.
-/

namespace OMA.S_oeis_a181411

open Filter
open scoped ArithmeticFunction.sigma

/-- The sum defining A181411 on positive indices. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * σ 1 (n + k)

theorem main :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => (Real.pi ^ 2 / 4) * (n : ℝ) * (2 : ℝ) ^ n) := by
  sorry

end OMA.S_oeis_a181411
