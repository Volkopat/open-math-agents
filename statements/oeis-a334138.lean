import Mathlib

/-!
# A334138: Number of ways to write n as x^4 + y*(2*y+1) + z*(3*z+1), where x is a nonnegative integer, and y and z are integers.

Source: https://oeis.org/A334138
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A334138 (Zhi-Wei Sun, Apr 15 2020), Conjecture 1: a(n)
= 0 only for n = 64. In other words, any nonnegative integer n not equal to 64 can be written as
x^4 + y*(2*y+1) + z*(3*z+1) with x,y,z integers.

Conventions:
* The sequence has offset 0 (data 1, 2, 2, 3, 3, 3, 3, 2, 2, 1, 3, 4, ...). `a n` is the number of
  triples (x, y, z) with x a natural number, y and z integers and n = x^4 + y*(2*y+1) + z*(3*z+1),
  exactly as in the OEIS name.
* Integer variables range over `ℤ`; the equation and the side conditions involving them are stated
  in `ℤ`, with the natural variables and n cast.
* `a(n) = 0 only for n = 64` is rendered literally as an only-if, for every n >= 0: a(n) = 0
  implies n = 64.
* Only Conjecture 1 of the entry is formalized.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a334138

/-- The condition in the name of A334138 on a tuple, for a given n. -/
def P (n : ℕ) (x : ℕ) (y z : ℤ) : Prop :=
  (x : ℤ) ^ 4 + y * (2 * y + 1) + z * (3 * z + 1) = (n : ℤ)

/-- A334138: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℤ × ℤ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A334138. -/
theorem main : ∀ n : ℕ, a n = 0 → n = 64 := by
  sorry

end OMA.S_oeis_a334138
