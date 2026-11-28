import Mathlib

/-!
# A145553: Numbers n such that n^2 can be expressed as the sum of 2 positive cubes in exactly 2 different ways.

Source: https://oeis.org/A145553
Credit: @darealpandaboi

Conjecture: this is an infinite sequence.

Translation notes.
* Different ways are unordered: pairs 1 <= x <= y with x^3 + y^3 = m (x^3 + y^3 = y^3 + x^3 is
  one way).
* This reproduces the listed data: n^2 has exactly 2 ways for the first 15 terms, and an exhaustive search with n^2 below 5*10^10 finds exactly 77976 and 223587 (checked by computer).
-/

namespace OMA.S_oeis_a145553

/-- The number of ways to write m as x^3 + y^3 with 1 <= x <= y. -/
def r (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun t => t.1 ≤ t.2 ∧ t.1 ^ 3 + t.2 ^ 3 = m)).card

theorem main : {n : ℕ | r (n ^ 2) = 2}.Infinite := by
  sorry

end OMA.S_oeis_a145553
