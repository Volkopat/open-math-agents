import Mathlib.Algebra.IsPrimePow

/-!
# A073652: Every prime occurs as a gap between consecutive composite prime powers

Source: https://oeis.org/A073652 (Amarnath Murthy)
Credit: @Alienchisel

The endpoints are the terms of OEIS A025475 greater than 1, namely prime
powers with exponent at least 2. The gap from 1 to 4 is excluded, as in A073652.
-/

namespace OMA.S_oeis_a073652

/-- A prime power that is composite, equivalently a prime raised to an exponent at least 2. -/
def IsCompositePrimePower (n : ℕ) : Prop :=
  IsPrimePow n ∧ ¬ n.Prime

/-- The endpoints are consecutive in the increasing list of composite prime powers. -/
def ConsecutiveCompositePrimePowers (lower upper : ℕ) : Prop :=
  IsCompositePrimePower lower ∧ IsCompositePrimePower upper ∧ lower < upper ∧
    ∀ n : ℕ, lower < n → n < upper → ¬ IsCompositePrimePower n

theorem main : ∀ p : ℕ, p.Prime →
    ∃ lower upper : ℕ, ConsecutiveCompositePrimePowers lower upper ∧ upper - lower = p := by
  sorry

end OMA.S_oeis_a073652
