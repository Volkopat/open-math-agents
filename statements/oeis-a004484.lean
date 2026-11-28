import Mathlib

/-!
# A004484: Sprague-Grundy values for Wythoff's game

Conjectures of Chai Wah Wu, 5 April 2021.
Source: https://oeis.org/A004484
Move rules and row indexing: https://oeis.org/A004481
-/

namespace OMA.S_oeis_a004484

/-- A move reduces either coordinate, or both by the same positive amount. -/
def Move (a b c d : ℕ) : Prop :=
  (c < a ∧ d = b) ∨ (c = a ∧ d < b) ∨
    ∃ t : ℕ, 0 < t ∧ c + t = a ∧ d + t = b

/-- At each position the value is the least natural absent from its options.
    This specification determines the values by induction on the coordinate sum. -/
def IsGrundy (g : ℕ → ℕ → ℕ) : Prop :=
  ∀ a b : ℕ,
    (∀ c d : ℕ, Move a b c d → g c d ≠ g a b) ∧
    (∀ m : ℕ, m < g a b → ∃ c d : ℕ, Move a b c d ∧ g c d = m)

/-- The zero-indexed row with first coordinate 3 gives A004484. The
    generating-function identity is written after multiplication by its
    denominator, whose constant coefficient is 1. -/
theorem main : ∀ g : ℕ → ℕ → ℕ, IsGrundy g →
    (∀ n : ℕ, 14 < n →
      (g 3 n : ℤ) = (g 3 (n - 1) : ℤ) + (g 3 (n - 6) : ℤ) - (g 3 (n - 7) : ℤ)) ∧
    (let x : PowerSeries ℚ := PowerSeries.X
     let a : PowerSeries ℚ := PowerSeries.mk (fun n => (g 3 n : ℚ))
     a * (x^7 - x^6 - x + 1) =
       4*x^14 - 12*x^13 + 7*x^12 + x^11 + x^9 + 7*x^7 -
         2*x^6 - 2*x^5 - 4*x^4 + x^3 + x^2 + x + 3) := by
  sorry

end OMA.S_oeis_a004484
