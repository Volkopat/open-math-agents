import Mathlib

/-!
# A273826: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with x*y + y*z + z*w a fourth power, where x is a positive integer, y is a nonnegative integer, and z and w are integers.

Source: https://oeis.org/A273826
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A273826 (Zhi-Wei Sun, May 31 2016), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 16^k*m (k = 0,1,2,... and m = 1, 14, 56, 91, 184, 329,
355, 1016).

Conventions:
* The sequence has offset 1 (data 1, 5, 5, 3, 8, 6, 5, 4, 2, 11, 5, 5, ...). `a n` is the number
  of quadruples (x, y, z, w) with x a positive integer, y a natural number, z and w integers, x*y
  + y*z + z*w a fourth power and n = x^2 + y^2 + z^2 + w^2, exactly as in the OEIS name.
* Integer variables range over `ℤ`; the equation and the side conditions involving them are stated
  in `ℤ`, with the natural variables and n cast.
* A fourth power is c^4 for an integer c (0 included); since c^4 = (-c)^4, c is taken to be a
  natural number.
* Only part (i) of the conjecture is formalized; parts (ii) and (iii) are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a273826

/-- The condition in the name of A273826 on a tuple, for a given n. -/
def P (n : ℕ) (x y : ℕ) (z w : ℤ) : Prop :=
  0 < x ∧ (∃ c : ℕ, (x : ℤ) * (y : ℤ) + (y : ℤ) * z + z * w = (c : ℤ) ^ 4) ∧
    (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + z ^ 2 + w ^ 2 = (n : ℤ)

/-- A273826: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℤ × ℤ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A273826. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      (∃ k m : ℕ, m ∈ ({1, 14, 56, 91, 184, 329, 355, 1016} : Finset ℕ) ∧
      n = 16 ^ k * m))) := by
  sorry

end OMA.S_oeis_a273826
