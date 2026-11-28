import Mathlib

/-!
# A275299: Number of ordered ways to write n as x^3 + y^2 + z^2 + w^2 with x + y - z a square, where x,y,z,w are nonnegative integers with y <= z.

Source: https://oeis.org/A275299
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A275299 (Zhi-Wei Sun, Jul 22 2016), part (i): a(n) > 0
for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 5, 8, 20, 24, 59, 71, 79, 119, 184, 575, 743,
764, 1471, 2759.

Conventions:
* The sequence has offset 0 (data 1, 2, 3, 3, 2, 1, 3, 2, 1, 4, 4, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with y <= z, x + y - z a square and n = x^3 + y^2 +
  z^2 + w^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`; the
  quantity is computed in `ℤ` (with the natural variables cast), where a negative value is never a
  square.
* Only part (i) of the conjecture is formalized; part (ii) concerns other linear forms.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a275299

/-- The condition in the name of A275299 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  y ≤ z ∧ IsSquare ((x : ℤ) + (y : ℤ) - (z : ℤ)) ∧ x ^ 3 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A275299: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A275299. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 5, 8, 20, 24, 59, 71, 79, 119, 184, 575, 743, 764, 1471, 2759} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a275299
