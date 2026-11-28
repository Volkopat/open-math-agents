import Mathlib

/-!
# A145552: Square numbers which can be expressed as the sum of 2 positive cubes in exactly 2 different ways.

Source: https://oeis.org/A145552
Credit: @darealpandaboi

Conjecture: this is an infinite sequence.

Translation notes.
* Different ways are unordered: pairs 1 <= x <= y with x^3 + y^3 = m (x^3 + y^3 = y^3 + x^3 is
  one way).
* This reproduces the listed data: the first 15 terms have exactly 2 ways, and an exhaustive search below 5*10^10 finds exactly 6080256576 and 49991146569 (checked by computer).
-/

namespace OMA.S_oeis_a145552

/-- The number of ways to write m as x^3 + y^3 with 1 <= x <= y. -/
def r (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun t => t.1 ≤ t.2 ∧ t.1 ^ 3 + t.2 ^ 3 = m)).card

theorem main : {m : ℕ | IsSquare m ∧ r m = 2}.Infinite := by
  sorry

end OMA.S_oeis_a145552
