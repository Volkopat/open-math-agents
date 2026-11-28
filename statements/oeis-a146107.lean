import Mathlib

/-!
# A146107: Bell numbers (A000110) read mod 17.

Source: https://oeis.org/A146107
Credit: @prasledi

Conjecture (G. C. Greubel, Feb 01 2016, in the FORMULA section of A146107):
"a(n+51702516367896047761) = a(n)."

Formalization notes:
* `a n` is the `n`-th Bell number reduced mod 17, offset 0, as in the OEIS data
  1, 1, 2, 5, 15, 1, 16, ... Mathlib's `Nat.bell n` is the `n`-th Bell number (the number of
  partitions of a set with `n` elements, `Nat.bell 0 = 1`), i.e. A000110.
* The conjecture is stated for all `n ≥ 0`, the full range of the sequence.
-/

namespace OMA.S_oeis_a146107

/-- A146107: the Bell numbers read mod 17. -/
def a (n : ℕ) : ℕ := Nat.bell n % 17

/-- Greubel's conjecture: `a` is periodic with period `51702516367896047761`. -/
theorem main : ∀ n : ℕ, a (n + 51702516367896047761) = a n := by
  sorry

end OMA.S_oeis_a146107
