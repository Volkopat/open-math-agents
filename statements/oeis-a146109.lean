import Mathlib

/-!
# A146109: Bell numbers (A000110) read mod 19.

Source: https://oeis.org/A146109
Credit: @prasledi

Conjecture (G. C. Greubel, Feb 01 2016, in the FORMULA section of A146109):
"a(n+109912203092239643840221) = a(n)."

Formalization notes:
* `a n` is the `n`-th Bell number reduced mod 19, offset 0, as in the OEIS data
  1, 1, 2, 5, 15, 14, 13, 3, 17, 0, ... Mathlib's `Nat.bell n` is the `n`-th Bell number (the number of
  partitions of a set with `n` elements, `Nat.bell 0 = 1`), i.e. A000110.
* The conjecture is stated for all `n ≥ 0`, the full range of the sequence.
-/

namespace OMA.S_oeis_a146109

/-- A146109: the Bell numbers read mod 19. -/
def a (n : ℕ) : ℕ := Nat.bell n % 19

/-- The conjecture: `a` is periodic with period `109912203092239643840221`. -/
theorem main : ∀ n : ℕ, a (n + 109912203092239643840221) = a n := by
  sorry

end OMA.S_oeis_a146109
