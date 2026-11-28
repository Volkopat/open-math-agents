import Mathlib

/-!
# A290491: Number of ways to write 12*n+1 as x^2 + 4*y^2 + 8*z^4, where x and y are positive integers and z is a nonnegative integer.

Source: https://oeis.org/A290491
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A290491 (Zhi-Wei Sun, Aug 03 2017), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 4, 10, 18, 28, 39, 49, 98, 142, 163, 184, 208, 320, 382,
408, 814, 910, 1414, 2139, 2674, 3188, 3213, 4230, 6279, 25482.

Conventions:
* The sequence has offset 1 (data 2, 2, 2, 1, 2, 3, 2, 2, 2, 1, 3, 4, ...). `a n` is the number of
  triples (x, y, z) of natural numbers with x > 0, y > 0 and 12*n+1 = x^2 + 4*y^2 + 8*z^4, exactly
  as in the OEIS name.
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a290491

/-- The condition in the name of A290491 on a tuple, for a given n. -/
def P (n : ℕ) (x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ x ^ 2 + 4 * y ^ 2 + 8 * z ^ 4 = 12 * n + 1

/-- A290491: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A290491. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({4, 10, 18, 28, 39, 49, 98, 142, 163, 184, 208, 320, 382, 408, 814, 910, 1414,
        2139, 2674, 3188, 3213, 4230, 6279, 25482} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a290491
