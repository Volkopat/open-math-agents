import Mathlib

/-!
# A282426: Number of ways to write n as x^4 + 4*y^2 + z^2 + 3^k, where x,y,z are nonnegative integers and k is among 0,1,2,3,4.

Source: https://oeis.org/A282426
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A282426 (Zhi-Wei Sun, Feb 14 2017), part (i): a(n) > 0
for all n > 0.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 2, 3, 3, 3, 3, 3, 4, 3, 2, ...). `a n` is the number of
  quadruples (x, y, z, k) of natural numbers with k among 0, 1, 2, 3, 4 and n = x^4 + 4*y^2 + z^2
  + 3^k, exactly as in the OEIS name.
* Only part (i) of the conjecture is formalized; parts (ii) and (iii) concern other forms.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a282426

/-- The condition in the name of A282426 on a tuple, for a given n. -/
def P (n : ℕ) (x y z k : ℕ) : Prop :=
  k ≤ 4 ∧ x ^ 4 + 4 * y ^ 2 + z ^ 2 + 3 ^ k = n

/-- A282426: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A282426. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a282426
