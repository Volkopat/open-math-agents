import Mathlib

/-!
# A275344: Number of ordered ways to write n as x^2 + y^2 + z^2 + 2*w^2 with x + 2*y + 3*z a square, where x,y,z,w are nonnegative integers.

Source: https://oeis.org/A275344
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A275344 (Zhi-Wei Sun, Jul 24 2016), part (i): a(n) > 0
for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 1, 3, 5, 7, 14, 15, 16, 25, 30, 33, 84, 169,
225.

Conventions:
* The sequence has offset 0 (data 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x + 2*y + 3*z a square and n = x^2 + y^2 + z^2 +
  2*w^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* Only part (i) of the conjecture is formalized; part (ii) concerns other linear forms.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a275344

/-- The condition in the name of A275344 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  IsSquare (x + 2 * y + 3 * z) ∧ x ^ 2 + y ^ 2 + z ^ 2 + 2 * w ^ 2 = n

/-- A275344: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A275344. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 1, 3, 5, 7, 14, 15, 16, 25, 30, 33, 84, 169, 225} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a275344
