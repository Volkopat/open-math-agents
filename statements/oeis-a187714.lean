import Mathlib

/-!
# The least Riesel number divisible by three

Arkadiusz Wesolowski's conjecture in OEIS A187714 uses odd multipliers and positive
exponents. The conjectured minimum is over all such Riesel numbers divisible by three.

Source: https://oeis.org/A187714
Credit: @gdyan2022
-/

namespace OMA.S_oeis_a187714

/-- An odd natural multiplier whose shifted powers of two are all composite. -/
def IsRiesel (m : ℕ) : Prop :=
  Odd m ∧ ∀ k : ℕ, 1 ≤ k → 1 < m * 2 ^ k - 1 ∧ ¬ (m * 2 ^ k - 1).Prime

theorem main : IsLeast {m : ℕ | 3 ∣ m ∧ IsRiesel m} 7148695169714208807 := by
  sorry

end OMA.S_oeis_a187714
