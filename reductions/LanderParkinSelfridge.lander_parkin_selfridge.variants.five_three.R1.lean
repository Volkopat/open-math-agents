import FormalConjectures.Wikipedia.LanderParkinAndSelfridgeConjecture
import Mathlib

-- Reduction LanderParkinSelfridge.lander_parkin_selfridge.variants.five_three.R1 of the
-- Lander–Parkin–Selfridge case x₁⁵ + x₂⁵ + x₃⁵ ≠ y⁵.
-- Credit: @marcusbuffett

/-!
# x₁⁵ + x₂⁵ + x₃⁵ = y⁵: fifth-power congruence obstructions, and the open rest

* `H1` (congruences): for each `p ∈ {5, 11, 41, 71, 101}`, a solution of
  `x₁⁵ + x₂⁵ + x₃⁵ = y⁵` has an even number of the four terms `x₁, x₂, x₃, y` divisible by `p`
  (stated as: an odd pattern is not a solution). For `p = 11, 41, 71, 101` the nonzero fifth
  powers mod `p` form the subgroup of order `(p - 1) / 5`, which contains `-1`, and no three of
  them sum to `0`; for `p = 5` the same holds modulo `25`, where the fifth powers of units
  are `±1, ±7`.
* `H2` (open): no positive solution has an even divisibility pattern at all five primes.

`main` is a case split. The congruences only rule out patterns; they do not settle the
conjecture, which `H2` keeps.
-/

namespace OMA.R_LanderParkinSelfridge_lander_parkin_selfridge_variants_five_three_R1

/-- Odd divisibility patterns at 5, 11, 41, 71 or 101 give no solution. -/
def H1 : Prop :=
  ∀ p ∈ ({5, 11, 41, 71, 101} : Finset ℕ), ∀ x₁ x₂ x₃ y : ℕ,
    ¬ ((p ∣ x₁ ↔ p ∣ x₂) ↔ (p ∣ x₃ ↔ p ∣ y)) → x₁ ^ 5 + x₂ ^ 5 + x₃ ^ 5 ≠ y ^ 5

/-- The open part: solutions with even divisibility patterns at all five primes. -/
def H2 : Prop :=
  ∀ x₁ x₂ x₃ y : ℕ, 0 < x₁ → 0 < x₂ → 0 < x₃ → 0 < y →
    (∀ p ∈ ({5, 11, 41, 71, 101} : Finset ℕ), ((p ∣ x₁ ↔ p ∣ x₂) ↔ (p ∣ x₃ ↔ p ∣ y))) →
    x₁ ^ 5 + x₂ ^ 5 + x₃ ^ 5 ≠ y ^ 5

theorem main : H1 → H2 → type_of% @LanderParkinSelfridge.lander_parkin_selfridge.variants.five_three := by
  intro h1 h2 x₁ x₂ x₃ y h₁ h₂ h₃ hy
  by_cases hp : ∀ p ∈ ({5, 11, 41, 71, 101} : Finset ℕ), ((p ∣ x₁ ↔ p ∣ x₂) ↔ (p ∣ x₃ ↔ p ∣ y))
  · exact h2 x₁ x₂ x₃ y h₁ h₂ h₃ hy hp
  · push Not at hp
    obtain ⟨p, hpS, hpar⟩ := hp
    exact h1 p hpS x₁ x₂ x₃ y (by tauto)

end OMA.R_LanderParkinSelfridge_lander_parkin_selfridge_variants_five_three_R1
