import Mathlib

/-!
# A262357: Number of ordered ways to write n as w^2 + x^2 + y^2 + z^2 with w^2*x^2 + 5*x^2*y^2 + 80*y^2*z^2 + 20*z^2*w^2 a square, where w is a positive integer and x,y,z are nonnegative integers.

Source: https://oeis.org/A262357
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A262357 (Zhi-Wei Sun, Apr 17 2016), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 4^k*m (k = 0,1,2,... and m = 1, 3, 11, 43, 547, 763,
1739, 6783).

Conventions:
* The sequence has offset 1 (data 1, 2, 1, 1, 4, 3, 2, 2, 4, 5, 1, 1, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with w > 0, n = w^2 + x^2 + y^2 + z^2 and w^2*x^2 +
  5*x^2*y^2 + 80*y^2*z^2 + 20*z^2*w^2 a square, exactly as in the OEIS name.
* `a square` is the Mathlib predicate `IsSquare` (0 included).
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a262357

/-- The condition in the name of A262357 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  0 < w ∧ w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n ∧
  IsSquare (w ^ 2 * x ^ 2 + 5 * x ^ 2 * y ^ 2 + 80 * y ^ 2 * z ^ 2 + 20 * z ^ 2 * w ^ 2)

/-- A262357: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A262357. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      (∃ k m : ℕ, m ∈ ({1, 3, 11, 43, 547, 763, 1739, 6783} : Finset ℕ) ∧
      n = 4 ^ k * m))) := by
  sorry

end OMA.S_oeis_a262357
