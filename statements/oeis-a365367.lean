import Mathlib

/-!
# A365367: Number of steps for iteration of map x -> (5/3)*round(x) to reach an integer > n when started at n, or -1 if no such integer is ever reached.

Source: https://oeis.org/A365367
Credit: @keiichisince1986-bot

A365367 is the sequence `a(n)` named in the title. The entry states:
Conjecture: an integer will always be reached, i.e. a(n) > 0 for all n.

Conventions:
- `round` is Mathlib's `round` on `ℚ` (`round x = ⌊x + 1/2⌋`). All iterates are integers or have
  fractional part `1/3` or `2/3`, so no value is ever a half-integer and the tie-breaking rule of `round`
  does not matter.
- The offset is `1`, so `n ≥ 1`. A rational number is an integer exactly when its reduced denominator
  `den` is `1`.
-/

namespace OMA.S_oeis_a365367

/-- The map `x ↦ (5/3) · round(x)` on `ℚ`. -/
def f (x : ℚ) : ℚ := 5 / 3 * round x

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, (f^[m] n).den = 1 ∧ (n : ℚ) < f^[m] n := by
  sorry

end OMA.S_oeis_a365367
