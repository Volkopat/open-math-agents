import Mathlib

/-!
# A347562: Number of ways to write n as 16^w + x^2 + (y^2 + 23*z^4)/324, where w,x,y,z are nonnegative integers.

Source: https://oeis.org/A347562
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A347562 (Zhi-Wei Sun, Jan 23 2022): a(n) > 0 for all n
> 0.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 3, 1, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with n = 16^w + x^2 + (y^2 + 23*z^4)/324, exactly as
  in the OEIS name.
* The quotient (y^2 + 23*z^4)/324 is required to be an integer: the divisibility by 324 is a
  separate conjunct, and the natural-number division is then exact.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a347562

/-- The condition in the name of A347562 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  324 ∣ y ^ 2 + 23 * z ^ 4 ∧ 16 ^ w + x ^ 2 + (y ^ 2 + 23 * z ^ 4) / 324 = n

/-- A347562: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A347562. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a347562
