import Mathlib

/-!
# A282463: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers, x == y (mod 2) and z <= w such that both x and x^2 + 62*x*y + y^2 are squares.

Source: https://oeis.org/A282463
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A282463 (Zhi-Wei Sun, Feb 16 2017), part (i): a(n) > 0
for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 1, 3, 43, 723, 1723, 3571, 3911 and 16^k*m (k
= 0,1,2,... and m = 7, 23, 31, 71, 79, 143, 303, 1591).

Conventions:
* The sequence has offset 0 (data 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x == y (mod 2), z <= w, both x and x^2 + 62*x*y
  + y^2 squares, and n = x^2 + y^2 + z^2 + w^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* Only part (i) of the conjecture is formalized; part (ii) concerns other forms.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a282463

/-- The condition in the name of A282463 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x % 2 = y % 2 ∧ z ≤ w ∧ IsSquare x ∧ IsSquare (x ^ 2 + 62 * x * y + y ^ 2) ∧
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A282463: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A282463. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 1, 3, 43, 723, 1723, 3571, 3911} : Finset ℕ) ∨
      (∃ k m : ℕ, m ∈ ({7, 23, 31, 71, 79, 143, 303, 1591} : Finset ℕ) ∧
      n = 16 ^ k * m)) := by
  sorry

end OMA.S_oeis_a282463
