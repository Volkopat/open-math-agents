import Mathlib

/-!
# A146119: Bell numbers (A000110) read mod 29.

Source: https://oeis.org/A146119
Credit: @prasledi

Conjecture (in the FORMULA section of A146119):
"a(n+91703076898614683377208150526107718802981) = a(n)."

Formalization notes:
* `a n` is the `n`-th Bell number reduced mod 29, offset 0, as in the OEIS data
  1, 1, 2, 5, 15, 23, 0, 7, 22, 6, ... Mathlib's `Nat.bell n` is the `n`-th Bell number (the number of
  partitions of a set with `n` elements, `Nat.bell 0 = 1`), i.e. A000110.
* The conjecture is stated for all `n ≥ 0`, the full range of the sequence.
-/

namespace OMA.S_oeis_a146119

/-- A146119: the Bell numbers read mod 29. -/
def a (n : ℕ) : ℕ := Nat.bell n % 29

/-- The conjecture: `a` is periodic with period `91703076898614683377208150526107718802981`. -/
theorem main : ∀ n : ℕ, a (n + 91703076898614683377208150526107718802981) = a n := by
  sorry

end OMA.S_oeis_a146119
