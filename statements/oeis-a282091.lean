import Mathlib

/-!
# A282091: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x + y - z a cube of an integer, where x,y,z,w are nonnegative integers with x >= y <= z and x == y (mod 2).

Source: https://oeis.org/A282091
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A282091 (Zhi-Wei Sun, Feb 06 2017), part (i): a(n) > 0
for all n = 0,1,2,.... Also, any nonnegative integer can be written as x^2 + y^2 + z^2 + w^2 with
x,y,z,w nonnegative integers and x <= y <= z such that x + y - z is a cube of an integer.

Conventions:
* The sequence has offset 0 (data 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x >= y <= z, x == y (mod 2), x + y - z a cube of
  an integer, and n = x^2 + y^2 + z^2 + w^2, exactly as in the OEIS name.
* A cube of an integer is c^3 with c any integer (possibly negative or zero); x + y - z is
  computed in `ℤ`.
* Both sentences of part (i) are formalized, as a conjunction. Part (ii) concerns other
  polynomials and is not formalized.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a282091

/-- The condition in the name of A282091 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  y ≤ x ∧ y ≤ z ∧ x % 2 = y % 2 ∧ (∃ c : ℤ, (x : ℤ) + (y : ℤ) - (z : ℤ) = c ^ 3) ∧
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A282091: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A282091. -/
theorem main : (∀ n : ℕ, 0 < a n) ∧
    (∀ n : ℕ, ∃ x y z w : ℕ, x ≤ y ∧ y ≤ z ∧
      (∃ c : ℤ, (x : ℤ) + (y : ℤ) - (z : ℤ) = c ^ 3) ∧
      x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) := by
  sorry

end OMA.S_oeis_a282091
