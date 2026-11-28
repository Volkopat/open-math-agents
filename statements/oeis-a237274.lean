import Mathlib

/-!
# A237274: a(n) = A236283(n) mod 9.

Source: https://oeis.org/A237274
Credit: @agchua

Comment line of A237274 (no author or date given there):
  (Conjecture) This has period 18: repeat 2, 1, 4, 5, 1, 4, 2, 7, 7, 5, 7, 7, 2, 4, 1, 5, 4, 1.
Offset of A237274: 0 (data 2, 1, 4, 5, 1, 4, 2, 7, 7, ...).

The other sequence. A236283 (offset 1) is, by its name line, the number of orbits of triples of
{1,2,...,n} under the action of the dihedral group of order 2n. Its formula section gives the closed
form a(n) = (5 + 3*(-1)^n + 2*n^2)/4 (conjectured by Colin Barker, Jan 21 2014; proved there by
Andrew Howroyd, Jan 17 2020: The above conjectures are true and can be derived from the following
formulas for even and odd n). A237274 starts at n = 0 and uses A236283(0) = 2 (its comments:
A236283(0)=2 and A236283(-n) = A236283(n)), which is the value of this closed form at n = 0.
So A236283 is defined below by this closed form for every n >= 0; its numerator is always divisible
by 4, so the integer division is exact. a(n) = A236283(n) mod 9, a value in 0..8.

The conjecture is stated for every n >= 0: a(n) is entry number (n mod 18), counted from 0, of the
listed period.
-/

namespace OMA.S_oeis_a237274

/-- A236283(n) by the closed form of its formula section: (5 + 3*(-1)^n + 2*n^2)/4. -/
def A236283 (n : ℕ) : ℤ := (5 + 3 * (-1) ^ n + 2 * (n : ℤ) ^ 2) / 4

/-- A237274(n) = A236283(n) mod 9, n >= 0. -/
def a (n : ℕ) : ℤ := A236283 n % 9

/-- The conjecture: period 18, repeat 2, 1, 4, 5, 1, 4, 2, 7, 7, 5, 7, 7, 2, 4, 1, 5, 4, 1. -/
theorem main : ∀ n : ℕ,
    a n = ([2, 1, 4, 5, 1, 4, 2, 7, 7, 5, 7, 7, 2, 4, 1, 5, 4, 1] : List ℤ).getD (n % 18) 0 := by
  sorry

end OMA.S_oeis_a237274
