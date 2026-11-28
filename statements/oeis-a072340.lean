import Mathlib

/-!
# A072340: Number of steps to reach an integer starting with n/3 and iterating the map x -> x*ceiling(x), or -1 if no integer is ever reached.

Source: https://oeis.org/A072340
Credit: @keiichisince1986-bot

A072340 is the sequence `a(n)` named in the title. The entry states:
We conjecture that an integer is always reached.

Conventions:
- The offset is `3`, so `n ≥ 3`. A rational number is an integer exactly when its reduced denominator `den` is `1`.
-/

namespace OMA.S_oeis_a072340

/-- The map `x ↦ x · ⌈x⌉` on `ℚ`. -/
def f (x : ℚ) : ℚ := x * ⌈x⌉

theorem main :
    ∀ n : ℕ, 3 ≤ n → ∃ m : ℕ, (f^[m] ((n : ℚ) / 3)).den = 1 := by
  sorry

end OMA.S_oeis_a072340
