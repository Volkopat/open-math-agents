import Mathlib

/-!
# A271076: Number of ordered ways to write n as u^5 + v^4 + x^3 + 2*y^3 + 3*z^3, where u, v , x, y and z are nonnegative integers with v > 0.

Source: https://oeis.org/A271076
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A271076 (Zhi-Wei Sun, Apr 07 2016), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 1, 8, 9, 10, 11, 13, 14, 15, 16, 23, 24, 38, 39, 61, 76,
77, 104, 118, 188, 214, 229.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 1, 2, ...). `a n` is the number of
  quintuples (u, v, x, y, z) of natural numbers with v > 0 and n = u^5 + v^4 + x^3 + 2*y^3 +
  3*z^3, exactly as in the OEIS name.
* Only part (i) of the conjecture is formalized; parts (ii) and (iii) concern other polynomials.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a271076

/-- The condition in the name of A271076 on a tuple, for a given n. -/
def P (n : ℕ) (u v x y z : ℕ) : Prop :=
  0 < v ∧ u ^ 5 + v ^ 4 + x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n

/-- A271076: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2}

/-- The conjecture recorded in A271076. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({1, 8, 9, 10, 11, 13, 14, 15, 16, 23, 24, 38, 39, 61, 76, 77, 104, 118, 188, 214,
      229} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a271076
