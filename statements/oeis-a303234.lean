import Mathlib

/-!
# A303234: Numbers of the form x*(x+1)/2 + 2^y with x and y nonnegative integers.

Source: https://oeis.org/A303234
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): any integer n > 1 can be written as the sum of two terms of the current sequence.

Formalization notes:
* Terms are x(x+1)/2 + 2^y with x, y ≥ 0; the two terms may be equal.
* Controls (computed): every n with 1 < n < 10000 is a sum of two terms.
-/

namespace OMA.S_oeis_a303234

/-- `t` is a term: `t = x(x+1)/2 + 2^y`. -/
def IsTerm (t : ℕ) : Prop := ∃ x y : ℕ, x * (x + 1) / 2 + 2 ^ y = t

/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 1 < n → ∃ s t : ℕ, IsTerm s ∧ IsTerm t ∧ s + t = n := by
  sorry

end OMA.S_oeis_a303234
