import Mathlib

/-!
# A275738: Number of ordered ways to write n as w^2 + x^2*(1+y^2+z^2), where w,x,y,z are nonnegative integers with x > 0, y <= z and y == z (mod 2).

Source: https://oeis.org/A275738
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A275738 (Zhi-Wei Sun, Aug 07 2016): For any n > 0, we
have a(n) > 0, i.e., n can be written as w^2 + x^2*(1+(z-y)^2+(y+z)^2) = w^2 +
x^2*(1+2*y^2+2*z^2), where w,x,y,z are nonnegative integers with x > 0 and y <= z. Moreover, any
positive integer n not equal to 449 can be written as 4^k*(1+x^2+y^2) + z^2, where k,x,y,z are
nonnegative integers with x == y (mod 2).

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with x > 0, y <= z, y == z (mod 2) and n = w^2 +
  x^2*(1+y^2+z^2), exactly as in the OEIS name.
* The first sentence is formalized as a(n) > 0 for every n > 0 (the `i.e.` clause is the entry's
  own reformulation of it), and the `Moreover` sentence as a second conjunct.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a275738

/-- The condition in the name of A275738 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  0 < x ∧ y ≤ z ∧ y % 2 = z % 2 ∧ w ^ 2 + x ^ 2 * (1 + y ^ 2 + z ^ 2) = n

/-- A275738: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A275738. -/
theorem main : (∀ n : ℕ, 0 < n → 0 < a n) ∧
    (∀ n : ℕ, 0 < n → n ≠ 449 → ∃ k x y z : ℕ, x % 2 = y % 2 ∧
      4 ^ k * (1 + x ^ 2 + y ^ 2) + z ^ 2 = n) := by
  sorry

end OMA.S_oeis_a275738
