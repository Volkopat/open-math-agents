import Mathlib

/-!
# A087677: Consider recurrence b(0) = n/3, b(n) = b(0)*floor(b(n-1)); sequence gives first integer reached, or -1 if no integer is ever reached.

Source: https://oeis.org/A087677
Credit: @keiichisince1986-bot

A087677 is the sequence `a(n)` named in the title. The entry states:
It is conjectured that an integer is always reached if the initial value is >= 2.

Conventions:
- The offset is `6`, i.e. the initial value `n/3` is at least `2`. The recurrence multiplies by the
  fixed number `b(0) = n/3`: `b(k) = g (n/3) (b(k-1))` with `g c x = c · ⌊x⌋`. A rational number is an integer exactly when its reduced denominator `den` is `1`.
-/

namespace OMA.S_oeis_a087677

/-- One step of the recurrence: `x ↦ c · ⌊x⌋`, with `c = b(0)`. -/
def g (c x : ℚ) : ℚ := c * ⌊x⌋

theorem main :
    ∀ n : ℕ, 6 ≤ n → ∃ m : ℕ, ((g ((n : ℚ) / 3))^[m] ((n : ℚ) / 3)).den = 1 := by
  sorry

end OMA.S_oeis_a087677
