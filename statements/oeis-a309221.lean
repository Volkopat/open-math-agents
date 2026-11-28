import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Rat.Defs

/-!
# OEIS A309221: the expected number of distinct squares visited by a knight

A walk starts at the origin of the infinite chessboard. Each step is a uniform
choice among the eight knight moves, independently of the previous choices.
The numerator and denominator in A326954 and A326955 represent the exact
expected number of distinct squares visited, including the starting square.

Source: https://oeis.org/A309221
Credit: @wtho704
-/

namespace OMA.S_oeis_a309221

/-- The first bit exchanges the two lengths; the other bits negate x and y. -/
abbrev Move := Bool × Bool × Bool

def jump (m : Move) : ℤ × ℤ :=
  let x : ℤ := if m.1 then 2 else 1
  let y : ℤ := if m.1 then 1 else 2
  (if m.2.1 then -x else x, if m.2.2 then -y else y)

/-- The origin together with the squares reached by the successive moves. -/
def visited : List Move → Finset (ℤ × ℤ)
  | [] => {0}
  | m :: ms => insert 0 ((visited ms).image (fun p => jump m + p))

/-- All length-n move sequences have probability 1/8^n. -/
def expectedRange (n : ℕ) : ℚ :=
  ((∑ w : Fin n → Move, (visited (List.ofFn w)).card : ℕ) : ℚ) / 8 ^ n

/-- The source sets the zeroth term separately and normalizes every positive term. -/
def a : ℕ → ℚ
  | 0 => 1
  | n + 1 => 2 ^ (3 * (n + 1) - 3) * expectedRange (n + 1)

theorem main : ∀ n : ℕ, ∃ z : ℤ, a n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a309221
