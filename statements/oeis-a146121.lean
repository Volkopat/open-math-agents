import Mathlib

/-!
# A146121: Bell numbers (A000110) read mod 31.

Source: https://oeis.org/A146121
Credit: @prasledi

Conjecture (G. C. Greubel, Feb 02 2016, in the FORMULA section of A146121):
"a(n+568972471024107865287021434301977158534824481) = a(n)."

Formalization notes:
* `a n` is the `n`-th Bell number reduced mod 31, offset 0, as in the OEIS data
  1, 1, 2, 5, 15, 21, 17, 9, 17, 5, ... Mathlib's `Nat.bell n` is the `n`-th Bell number (the number of
  partitions of a set with `n` elements, `Nat.bell 0 = 1`), i.e. A000110.
* The conjecture is stated for all `n ≥ 0`, the full range of the sequence.
-/

namespace OMA.S_oeis_a146121

/-- A146121: the Bell numbers read mod 31. -/
def a (n : ℕ) : ℕ := Nat.bell n % 31

/-- The conjecture: `a` is periodic with period `568972471024107865287021434301977158534824481`. -/
theorem main : ∀ n : ℕ, a (n + 568972471024107865287021434301977158534824481) = a n := by
  sorry

end OMA.S_oeis_a146121
