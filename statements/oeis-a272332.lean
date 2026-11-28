import Mathlib

/-!
# A272332: Number of ordered ways to write n as w^2 + x^2 + y^2 + z^2 with 36*x^2*y + 12*y^2*z + z^2*x a square, where w is a positive integer and x,y,z are nonnegative integers.

Source: https://oeis.org/A272332
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A272332 (Zhi-Wei Sun, Apr 26 2016): a(n) > 0 for all n
> 0, and a(n) = 1 only for n = 16^k*m (k = 0,1,2,... and m = 1, 79, 591, 599, 1752, 1839, 10264).

Conventions:
* The sequence has offset 1 (data 1, 3, 2, 2, 6, 4, 3, 3, 3, 8, 5, 2, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with w > 0, 36*x^2*y + 12*y^2*z + z^2*x a square and
  n = w^2 + x^2 + y^2 + z^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a272332

/-- The condition in the name of A272332 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  0 < w ∧ IsSquare (36 * x ^ 2 * y + 12 * y ^ 2 * z + z ^ 2 * x) ∧ w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n

/-- A272332: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A272332. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      (∃ k m : ℕ, m ∈ ({1, 79, 591, 599, 1752, 1839, 10264} : Finset ℕ) ∧
      n = 16 ^ k * m))) := by
  sorry

end OMA.S_oeis_a272332
