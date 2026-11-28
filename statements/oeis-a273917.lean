import Mathlib

/-!
# A273917: Number of ordered ways to write n as w^2 + 3*x^2 + y^4 + z^5, where w is a positive integer and x,y,z are nonnegative integers.

Source: https://oeis.org/A273917
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A273917 (Zhi-Wei Sun, Jun 04 2016), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 1, 3, 7, 11, 12, 15, 19, 24, 27, 31, 34, 35, 43, 46, 47,
56, 70, 71, 72, 87, 88, 115, 136, 137, 147, 167, 168, 178, 207, 235, 236, 267, 286, 297, 423, 537,
747, 762, 1017.

Conventions:
* The sequence has offset 1 (data 1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with w > 0 and n = w^2 + 3*x^2 + y^4 + z^5, exactly
  as in the OEIS name.
* Only part (i) of the conjectures is formalized; part (ii) concerns another form.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a273917

/-- The condition in the name of A273917 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  0 < w ∧ w ^ 2 + 3 * x ^ 2 + y ^ 4 + z ^ 5 = n

/-- A273917: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A273917. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({1, 3, 7, 11, 12, 15, 19, 24, 27, 31, 34, 35, 43, 46, 47, 56, 70, 71, 72, 87, 88,
        115, 136, 137, 147, 167, 168, 178, 207, 235, 236, 267, 286, 297, 423, 537, 747, 762,
        1017} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a273917
