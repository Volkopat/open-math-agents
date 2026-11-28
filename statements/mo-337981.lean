import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Rat.Defs

/-! Source: https://mathoverflow.net/questions/337981 -/

open scoped BigOperators

namespace OMA.S_mo_337981

def divisorVariance (n : ℕ) : ℚ :=
  let D := n.divisors
  let mean : ℚ := (∑ d ∈ D, (d : ℚ)) / D.card
  (∑ d ∈ D, ((d : ℚ) - mean) ^ 2) / D.card

theorem main : ∀ m n : ℕ, 2 ≤ m → 2 ≤ n →
    (m : ℚ) / divisorVariance m = (n : ℚ) / divisorVariance n → m = n := by
  sorry

end OMA.S_mo_337981
