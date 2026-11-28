import Mathlib

/-!
# A076218: Numbers n such that 2*n^2 - 3*n + 1 is a square.

Source: https://oeis.org/A076218
Credit: @agchua

Comment of A076218 (J. Lowell, Jul 23 2016; the entry is by Gregory V. Richardson, Nov 03 2002):
  Conjecture: a nonzero number occurs twice in A055524 if and only if it's in this sequence.
A055524 (offset 3) is the longest other side of a Pythagorean triangle with n as length of one of
the three sides; as that entry says, n is then a leg and A055524(n) the hypotenuse. So
A055524(n) is the largest c such that n^2 + b^2 = c^2 for some b >= 1. A number x occurs twice
in A055524 when exactly two indices t >= 3 have A055524(t) = x. A number x is in A076218 when
2*x^2 - 3*x + 1 is the square of an integer.
Range: the literal claim fails at x = 1 for a trivial reason. 1 is a term of A076218
(2 - 3 + 1 = 0 = 0^2) but does not occur in A055524, whose values are at least 5; this term comes
from the degenerate solution x - 1 = 0^2, 2*x - 1 = 1^2. So the claim is stated for x >= 2.
-/

namespace OMA.S_oeis_a076218

/-- A055524(n): the largest hypotenuse c of a Pythagorean triangle with a leg of length n. -/
noncomputable def A055524 (n : ℕ) : ℕ := sSup {c : ℕ | ∃ b : ℕ, 0 < b ∧ n ^ 2 + b ^ 2 = c ^ 2}

/-- x is a term of A076218: 2*x^2 - 3*x + 1 is a square. -/
def IsTerm (x : ℕ) : Prop := IsSquare (2 * (x : ℤ) ^ 2 - 3 * x + 1)

/-- The conjecture, for x >= 2: x occurs exactly twice in A055524 iff x is a term of A076218. -/
theorem main : ∀ x : ℕ, 2 ≤ x →
    ({t : ℕ | 3 ≤ t ∧ A055524 t = x}.ncard = 2 ↔ IsTerm x) := by
  sorry

end OMA.S_oeis_a076218
