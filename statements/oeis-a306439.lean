import Mathlib

/-!
# A306439: Number of ways to write n as x*(3x+1)/2 + y*(3y+1)/2 + z*(3z+1) + 3w*(3w+1)/2, where x,y,z,w are nonnegative integers with x <= y.

Source: https://oeis.org/A306439
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A306439 (Zhi-Wei Sun, Feb 15 2019), Conjecture 1: a(n)
> 0 for all n > 5, and a(n) = 1 only for n = 0, 2, 7, 9, 11, 12, 16, 31, 33, 41.

Conventions:
* The sequence has offset 0 (data 1, 0, 1, 0, 2, 0, 2, 1, 2, 1, 2, 1, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x <= y and n = x*(3x+1)/2 + y*(3y+1)/2 +
  z*(3z+1) + 3w*(3w+1)/2, exactly as in the OEIS name.
* The divisions by 2 are natural-number divisions and are exact, because k*(3k+1) is always even.
* The positivity part is stated for n > 5 and the only-if part for every n >= 0 (the offset).
* Only Conjecture 1 of the entry is formalized; Conjecture 2 concerns other forms.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a306439

/-- The condition in the name of A306439 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ≤ y ∧ x * (3 * x + 1) / 2 + y * (3 * y + 1) / 2 + z * (3 * z + 1) + 3 * w * (3 * w + 1) / 2 = n

/-- A306439: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A306439. -/
theorem main : ∀ n : ℕ, (5 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a306439
