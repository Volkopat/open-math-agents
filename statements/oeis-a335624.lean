import Mathlib

/-!
# A335624: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x + 3*y + 4*z a square, where x, y, z, w are nonnegative integers.

Source: https://oeis.org/A335624
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A335624 (Zhi-Wei Sun, Oct 08 2020): a(n) > 0 if n is
not divisible by 8. Moreover, a(n) = 0 if and only if n has the form 2^(4k+3)*m (k >= 0 and m = 1,
3, 5, 43).

Conventions:
* The sequence has offset 0 (data 1, 3, 3, 1, 1, 3, 3, 1, 0, 3, 4, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x + 3*y + 4*z a square and n = x^2 + y^2 + z^2 +
  w^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* Both sentences are formalized, as a conjunction.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a335624

/-- The condition in the name of A335624 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  IsSquare (x + 3 * y + 4 * z) ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A335624: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A335624. -/
theorem main : (∀ n : ℕ, ¬ 8 ∣ n → 0 < a n) ∧
    (∀ n : ℕ, a n = 0 ↔
      ∃ k m : ℕ, m ∈ ({1, 3, 5, 43} : Finset ℕ) ∧ n = 2 ^ (4 * k + 3) * m) := by
  sorry

end OMA.S_oeis_a335624
