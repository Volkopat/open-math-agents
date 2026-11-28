import Mathlib

/-!
# A306260: Number of ways to write n as w*(4w+1) + x*(4x-1) + y*(4y-2) + z*(4z-3) with w,x,y,z nonnegative integers.

Source: https://oeis.org/A306260
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A306260 (Zhi-Wei Sun, Feb 01 2019), Conjecture 1: a(n)
> 0 for all n >= 0, and a(n) = 1 only for n = 0, 1, 2, 4, 7, 9, 11, 14, 23, 25, 28, 37.

Conventions:
* The sequence has offset 0 (data 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with n = w*(4w+1) + x*(4x-1) + y*(4y-2) + z*(4z-3),
  exactly as in the OEIS name.
* The subtractions such as 4*x - 1 are natural-number subtractions; they are truncated only when
  the variable is 0, where the corresponding product is 0 in any case.
* Only Conjecture 1 of the entry is formalized; Conjecture 2 concerns another form.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a306260

/-- The condition in the name of A306260 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  w * (4 * w + 1) + x * (4 * x - 1) + y * (4 * y - 2) + z * (4 * z - 3) = n

/-- A306260: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A306260. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 1, 2, 4, 7, 9, 11, 14, 23, 25, 28, 37} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a306260
