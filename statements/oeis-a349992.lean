import Mathlib

/-!
# A349992: Number of ways to write n as x^4 + y^2 + (z^2 + 2*4^w)/3, where x, y, z are nonnegative integers, and w is 0 or 1.

Source: https://oeis.org/A349992
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A349992 (Zhi-Wei Sun, Dec 08 2021), Conjecture 1: a(n)
> 0 for all n > 0, and a(n) = 1 only for n = 1, 30, 64, 80, 302, 350, 472, 480, 847, 3497, 13582,
25630, 38064.

Conventions:
* The sequence has offset 1 (data 1, 3, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with w equal to 0 or 1 and n = x^4 + y^2 + (z^2 +
  2*4^w)/3, exactly as in the OEIS name.
* The quotient (z^2 + 2*4^w)/3 is required to be an integer: the divisibility by 3 is a separate
  conjunct, and the natural-number division is then exact.
* Only Conjecture 1 of the entry is formalized.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a349992

/-- The condition in the name of A349992 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  w ≤ 1 ∧ 3 ∣ z ^ 2 + 2 * 4 ^ w ∧ x ^ 4 + y ^ 2 + (z ^ 2 + 2 * 4 ^ w) / 3 = n

/-- A349992: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A349992. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({1, 30, 64, 80, 302, 350, 472, 480, 847, 3497, 13582, 25630, 38064} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a349992
