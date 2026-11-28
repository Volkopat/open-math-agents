import Mathlib

/-!
# A275150: Number of ordered ways to write n as x^3 + 2*y^2 + k*z^2, where x,y,z are nonnegative integers, k is 1 or 5, and k = 1 if z = 0.

Source: https://oeis.org/A275150
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A275150 (Zhi-Wei Sun, Jul 17 2016), Conjecture 1: a(n)
> 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 15, 79, 120, 218, 399, 454, 622, 725,
3240.

Conventions:
* The sequence has offset 0 (data 1, 2, 2, 2, 2, 2, 2, 2, 3, 4, 3, 2, ...). `a n` is the number of
  quadruples (x, y, z, k) of natural numbers with k = 1 or k = 5, k = 1 if z = 0, and n = x^3 +
  2*y^2 + k*z^2, exactly as in the OEIS name.
* Only Conjecture 1 of the entry is formalized; Conjecture 2 is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a275150

/-- The condition in the name of A275150 on a tuple, for a given n. -/
def P (n : ℕ) (x y z k : ℕ) : Prop :=
  (k = 1 ∨ k = 5) ∧ (z = 0 → k = 1) ∧ x ^ 3 + 2 * y ^ 2 + k * z ^ 2 = n

/-- A275150: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A275150. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 15, 79, 120, 218, 399, 454, 622, 725, 3240} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a275150
