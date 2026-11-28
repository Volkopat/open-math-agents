import Mathlib

/-!
# A273404: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with x + 24*y a square, where x,y,z,w are nonnegative integers with z <= w.

Source: https://oeis.org/A273404
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A273404 (Zhi-Wei Sun, May 21 2016): a(n) > 0 for all n
= 0,1,2,..., and a(n) = 1 only for n = 0, 16^k*m (k = 0,1,2,... and m = 8, 12, 23, 24, 47, 71,
168, 344, 632).

Conventions:
* The sequence has offset 0 (data 1, 2, 3, 2, 2, 3, 3, 2, 1, 3, 4, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with z <= w, x + 24*y a square and n = x^2 + y^2 +
  z^2 + w^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a273404

/-- The condition in the name of A273404 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  z ≤ w ∧ IsSquare (x + 24 * y) ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A273404: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A273404. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n = 0 ∨
      (∃ k m : ℕ, m ∈ ({8, 12, 23, 24, 47, 71, 168, 344, 632} : Finset ℕ) ∧
      n = 16 ^ k * m)) := by
  sorry

end OMA.S_oeis_a273404
