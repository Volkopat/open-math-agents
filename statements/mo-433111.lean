import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Function

/-! Source: https://mathoverflow.net/questions/433111, question 1. -/

namespace OMA.S_mo_433111

open scoped BigOperators

theorem main :
    ∀ N : ℕ, 0 < N → ∀ x : ℕ → ℕ,
      let n := N.divisors.card
      Set.BijOn x (Set.Iio n) (↑N.divisors : Set ℕ) →
      (n : ℚ) / 2 ≤
        ∑ i ∈ Finset.range n, (x i : ℚ) /
          ((x ((i + 1) % n) : ℚ) + (x ((i + 2) % n) : ℚ)) := by
  sorry

end OMA.S_mo_433111
