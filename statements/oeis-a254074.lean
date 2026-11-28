import Mathlib

/-!
# Decimal digits of a number and its square

Felix Fröhlich introduced OEIS A254074 in 2015. Chai Wah Wu conjectured in
2017 that no term is divisible by five.
Source: https://oeis.org/A254074 (OEIS Foundation, CC BY-SA 4.0).
Credit: @anmolspace (Lean formalization).
-/

namespace OMA.S_oeis_a254074

/-- The decimal digits have minimum five and maximum nine, both attained. -/
def digitExtrema (n : ℕ) : Prop :=
  5 ∈ Nat.digits 10 n ∧ 9 ∈ Nat.digits 10 n ∧
    ∀ d ∈ Nat.digits 10 n, 5 ≤ d ∧ d ≤ 9

/-- The digit conditions apply separately to the number and its square. -/
def isTerm (n : ℕ) : Prop := digitExtrema n ∧ digitExtrema (n ^ 2)

/-- Chai Wah Wu's conjecture of September 10, 2017. -/
theorem main : ∀ n : ℕ, isTerm n → ¬ 5 ∣ n := by
  sorry

end OMA.S_oeis_a254074
