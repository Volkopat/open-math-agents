import Mathlib

/-!
# A258020: fixed points of the map `x ↦ ⌊tan x⌋`

Source: https://oeis.org/A258020
Credit: @Lenqth

A258020(n) is the number of steps needed to reach a fixed point of the map `x ↦ ⌊tan x⌋` when
iterating from `x = n`. The map sends integers to integers and is defined on all of `ℤ` (the
entry notes this explicitly), and the iteration is only well defined if every orbit reaches a
fixed point.

Formalizes the statement in the example section of A258020: the only known fixed points of
`x ↦ ⌊tan x⌋` are `0` and `1`, and it is conjectured that there are no others. That is, for every
integer `n`, `⌊tan n⌋ = n` implies `n = 0` or `n = 1`.
-/

namespace OMA.S_oeis_a258020

/-- The only integer fixed points of `x ↦ ⌊tan x⌋` are `0` and `1`. -/
theorem main : ∀ n : ℤ, ⌊Real.tan n⌋ = n → n = 0 ∨ n = 1 := by
  sorry

end OMA.S_oeis_a258020
