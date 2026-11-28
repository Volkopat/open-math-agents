import Mathlib

/-!
# A270966: Number of ways to write n as x^2 + y^2 + z*(3z+1)/2, where x, y and z are integers with 0 <= x <= y such that x or y has the form p-1 with p prime.

Source: https://oeis.org/A270966
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A270966 (Zhi-Wei Sun, Mar 27 2016), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 1, 49, 608.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 2, 2, 3, 2, 2, 3, 3, 2, 2, ...). `a n` is the number of
  triples (x, y, z) with x, y natural numbers, z an integer, 0 <= x <= y and n = x^2 + y^2 +
  z*(3z+1)/2, such that x or y has the form p - 1 with p prime, exactly as in the OEIS name.
* z ranges over all integers (`ℤ`), and the equation is stated in `ℤ` with x, y, n cast; z*(3z+1)
  is always even, so the integer division by 2 is exact.
* `x has the form p - 1 with p prime` is `(x + 1).Prime`, and likewise for y.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a270966

/-- The condition in the name of A270966 on a tuple, for a given n. -/
def P (n : ℕ) (x y : ℕ) (z : ℤ) : Prop :=
  x ≤ y ∧ (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + z * (3 * z + 1) / 2 = n ∧ ((x + 1).Prime ∨ (y + 1).Prime)

/-- A270966: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℤ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A270966. -/
theorem main : ∀ n : ℕ, 0 < n → ((0 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({1, 49, 608} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a270966
