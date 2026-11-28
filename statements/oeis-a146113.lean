import Mathlib

/-!
# A146113: Bell numbers (A000110) read mod 23.

Source: https://oeis.org/A146113
Credit: @prasledi

Conjecture (G. C. Greubel, Feb 02 2016, in the FORMULA section of A146113):
"a(n+949112181811268728834319677753) = a(n)."

Formalization notes:
* `a n` is the `n`-th Bell number reduced mod 23, offset 0, as in the OEIS data
  1, 1, 2, 5, 15, 6, 19, 3, 0, 10, ... Mathlib's `Nat.bell n` is the `n`-th Bell number (the number of
  partitions of a set with `n` elements, `Nat.bell 0 = 1`), i.e. A000110.
* The conjecture is stated for all `n ≥ 0`, the full range of the sequence.
-/

namespace OMA.S_oeis_a146113

/-- A146113: the Bell numbers read mod 23. -/
def a (n : ℕ) : ℕ := Nat.bell n % 23

/-- The conjecture: `a` is periodic with period `949112181811268728834319677753`. -/
theorem main : ∀ n : ℕ, a (n + 949112181811268728834319677753) = a n := by
  sorry

end OMA.S_oeis_a146113
