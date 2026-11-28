import Mathlib

/-!
# A273108: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with (x + y)^2 + (4z)^2 a square, where x,y,z,w are nonnegative integers with x <= y > z.

Source: https://oeis.org/A273108
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A273108 (Zhi-Wei Sun, May 15 2016), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 39, 47, 95, 543, 4^k*m (k = 0,1,2,... and m = 1, 3, 7,
15, 23, 135, 183).

Conventions:
* The sequence has offset 1 (data 1, 2, 1, 1, 3, 3, 1, 2, 3, 5, 3, 1, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x <= y > z, (x+y)^2 + (4*z)^2 a square and n =
  x^2 + y^2 + z^2 + w^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* Only part (i) of the conjecture is formalized; part (ii) concerns other forms.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a273108

/-- The condition in the name of A273108 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ≤ y ∧ z < y ∧ IsSquare ((x + y) ^ 2 + (4 * z) ^ 2) ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A273108: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A273108. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({39, 47, 95, 543} : Finset ℕ) ∨
      (∃ k m : ℕ, m ∈ ({1, 3, 7, 15, 23, 135, 183} : Finset ℕ) ∧ n = 4 ^ k * m))) := by
  sorry

end OMA.S_oeis_a273108
