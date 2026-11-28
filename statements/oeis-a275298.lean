import Mathlib

/-!
# A275298: Number of ordered ways to write n as w^3 + x^2 + y^2 + z^2 with x - w a square, where x,y,z,w are nonnegative integers with y <= z > w.

Source: https://oeis.org/A275298
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A275298 (Zhi-Wei Sun, Jul 22 2016), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 1, 3, 4, 7, 8, 12, 16, 23, 24, 40, 47, 71, 167, 311, 599.

Conventions:
* The sequence has offset 1 (data 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with y <= z > w, x - w a square and n = w^3 + x^2 +
  y^2 + z^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`; the
  quantity is computed in `ℤ` (with the natural variables cast), where a negative value is never a
  square.
* Only part (i) of the conjecture is formalized; part (ii) concerns other linear forms.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a275298

/-- The condition in the name of A275298 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  y ≤ z ∧ w < z ∧ IsSquare ((x : ℤ) - (w : ℤ)) ∧ w ^ 3 + x ^ 2 + y ^ 2 + z ^ 2 = n

/-- A275298: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A275298. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({1, 3, 4, 7, 8, 12, 16, 23, 24, 40, 47, 71, 167, 311, 599} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a275298
