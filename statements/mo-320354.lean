import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Defs

/-!
# A zero digit in sufficiently large bases

Source: https://mathoverflow.net/questions/320354/on-a-much-weaker-version-of-the-normal-conjecture
Credit: @MMexicann
-/

namespace OMA.S_mo_320354

/-- The digit in position i + 1 after the radix point in the base-b expansion of the absolute value. -/
noncomputable def fractionalDigit (b i : ℕ) (x : ℝ) : ℤ :=
  ⌊(b : ℝ) ^ (i + 1) * |x|⌋ % (b : ℤ)

theorem main :
    ∀ x : ℝ, IsAlgebraic ℚ x → Irrational x →
      ∃ B : ℕ, ∀ b : ℕ, 2 ≤ b → B ≤ b → ∃ i : ℕ, fractionalDigit b i x = 0 := by
  sorry

end OMA.S_mo_320354
