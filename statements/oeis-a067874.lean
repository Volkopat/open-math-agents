import Mathlib

/-!
# A067874: Positive integers x satisfying x^2 - D*y^2 = 1 for a unique integer D.

Source: https://oeis.org/A067874
Credit: @divmxnd0x

Conjecture (Griffin N. Macris, Apr 11 2016, stated in A067874): all terms of A002110 greater
than 1 (the primorials `p#`, `p` prime) are terms of this sequence.

Formalization notes:
* `x` is a term iff `x > 0` and exactly one integer `D` admits an integer `y` with
  `x^2 - D y^2 = 1` (data `2, 4, 6, 12, 14, ...`; `x = 1` is not a term since then every `D` works
  with `y = 0`).
* The terms of A002110 greater than 1 are `primorial p` for primes `p` (`2, 6, 30, 210, ...`).
-/

namespace OMA.S_oeis_a067874

/-- `x` is a term: `x > 0` and `x^2 - D y^2 = 1` has a solution `y` for exactly one integer `D`. -/
def IsTerm (x : ℕ) : Prop :=
  0 < x ∧ ∃! D : ℤ, ∃ y : ℤ, (x : ℤ) ^ 2 - D * y ^ 2 = 1

/-- Macris' conjecture: every primorial `p#` (`p` prime) is a term. -/
theorem main : ∀ p : ℕ, p.Prime → IsTerm (primorial p) := by
  sorry

end OMA.S_oeis_a067874
