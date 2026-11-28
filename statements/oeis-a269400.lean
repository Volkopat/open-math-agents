import Mathlib

/-!
# A269400: Number of ordered ways to write n as w^2 + x^2 + y^2 + z^2 with 6*w^2*x^2 + 12*x^2*y^2 + 52*y^2*z^2 + 27*z^2*w^2 a square, where w,x,y are nonnegative integers and z is a positive integer.

Source: https://oeis.org/A269400
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A269400 (Zhi-Wei Sun, Apr 16 2016), part (i), first
sentence: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 3, 15, 31, 39, 71, 79, 195, 311,
319, 403, 559, 591, 683, 719, 1031, 1439, 1643, 2519, 6879, 2^k, 2^(2k+1)*39 (k = 0,1,2,...).

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with z > 0, n = w^2 + x^2 + y^2 + z^2 and 6*w^2*x^2 +
  12*x^2*y^2 + 52*y^2*z^2 + 27*z^2*w^2 a square, exactly as in the OEIS name.
* `a square` is the Mathlib predicate `IsSquare` (0 included).
* Only the first sentence of part (i) is formalized; the `Also` sentence of part (i) and part (ii)
  are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a269400

/-- The condition in the name of A269400 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  0 < z ∧ w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n ∧
  IsSquare (6 * w ^ 2 * x ^ 2 + 12 * x ^ 2 * y ^ 2 + 52 * y ^ 2 * z ^ 2 + 27 * z ^ 2 * w ^ 2)

/-- A269400: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A269400. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({3, 15, 31, 39, 71, 79, 195, 311, 319, 403, 559, 591, 683, 719, 1031, 1439, 1643,
        2519, 6879} : Finset ℕ) ∨
      (∃ k : ℕ, n = 2 ^ k) ∨ (∃ k : ℕ, n = 2 ^ (2 * k + 1) * 39))) := by
  sorry

end OMA.S_oeis_a269400
