import Mathlib

/-!
# A087707: Number of steps for iteration of map x -> (5/3)*ceiling(x) to reach an integer > n when started at n, or -1 if no such integer is ever reached.

Source: https://oeis.org/A087707
Credit: @keiichisince1986-bot

A087707 is the sequence `a(n)` named in the title. The entry states:
It is conjectured that an integer is always reached.

Conventions:
- The offset is `1`, so `n ≥ 1`. The conjecture says that some iterate is an integer greater than `n`.
  A rational number is an integer exactly when its reduced denominator `den` is `1`.
-/

namespace OMA.S_oeis_a087707

/-- The map `x ↦ (5/3) ⌈x⌉` on `ℚ`. -/
def f (x : ℚ) : ℚ := 5 / 3 * ⌈x⌉

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, (f^[m] n).den = 1 ∧ (n : ℚ) < f^[m] n := by
  sorry

end OMA.S_oeis_a087707
