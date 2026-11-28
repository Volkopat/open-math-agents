import Mathlib

/-!
# A266968: Number of ordered ways to write n as x^5+y^4+z^3+w*(w+1)/2, where x, y, z and w are nonnegative integers with z > 0 and w > 0.

Source: https://oeis.org/A266968
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A266968 (Zhi-Wei Sun, Mar 28 2016), part (i): a(n) > 0
for all n > 1, and a(n) = 1 only for n = 2, 6, 7, 14, 21, 22, 26, 41, 51, 184, 189, 206, 225, 229,
526, 708.

Conventions:
* The sequence has offset 0 (data 0, 0, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with z > 0, w > 0 and n = x^5 + y^4 + z^3 +
  w*(w+1)/2, exactly as in the OEIS name.
* The division by 2 is natural-number division, which is exact because w*(w+1) is even.
* Only part (i) of the conjecture is formalized; parts (ii)-(v) concern other polynomials.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a266968

/-- The condition in the name of A266968 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  0 < z ∧ 0 < w ∧ x ^ 5 + y ^ 4 + z ^ 3 + w * (w + 1) / 2 = n

/-- A266968: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A266968. -/
theorem main : ∀ n : ℕ, (1 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({2, 6, 7, 14, 21, 22, 26, 41, 51, 184, 189, 206, 225, 229, 526, 708} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a266968
