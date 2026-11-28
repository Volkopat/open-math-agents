import Mathlib

/-!
# A283239: Number of ways to write n as x^2 + y^2 + z*(3*z-1)/2 with x,y,z integers such that x + 2*y is a square.

Source: https://oeis.org/A283239
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A283239 (Zhi-Wei Sun, Mar 03 2017), part (i): a(n) > 0
for all n >= 0, and a(n) = 1 only for n = 0, 8, 43, 84, 133, 253, 399, 488, 523, 803, 7369.

Conventions:
* The sequence has offset 0 (data 1, 2, 3, 2, 2, 5, 5, 5, 1, 2, 4, 2, ...). `a n` is the number of
  triples (x, y, z) of integers with n = x^2 + y^2 + z*(3*z-1)/2 and x + 2*y a square, exactly as
  in the OEIS name.
* x, y, z range over `ℤ` and the equation is stated in `ℤ` with n cast; z*(3z-1) is always even,
  so the integer division by 2 is exact.
* `a square` is `IsSquare` in `ℤ`, i.e. the square of an integer (a negative integer is never a
  square).
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a283239

/-- The condition in the name of A283239 on a tuple, for a given n. -/
def P (n : ℕ) (x y z : ℤ) : Prop :=
  x ^ 2 + y ^ 2 + z * (3 * z - 1) / 2 = n ∧ IsSquare (x + 2 * y)

/-- A283239: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℤ × ℤ × ℤ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A283239. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 8, 43, 84, 133, 253, 399, 488, 523, 803, 7369} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a283239
