import Mathlib

/-!
# A279612: Number of ways to write n = x^2 + y^2 + z^2 + w^2 with x + 2*y - 2*z a power of 4 (including 4^0 = 1), where x,y,z,w are nonnegative integers.

Source: https://oeis.org/A279612
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A279612 (Zhi-Wei Sun, Dec 15 2016), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 16^k*q (k = 0,1,2,... and q = 1, 2, 3, 6, 7, 8, 12, 15,
27, 31, 47, 72, 76, 92, 111, 127).

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 1, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x + 2*y - 2*z a power of 4 (4^0 = 1 included)
  and n = x^2 + y^2 + z^2 + w^2, exactly as in the OEIS name.
* The quantity x + 2*y - 2*z is computed in `ℤ` (it may be negative, in which case it is not a
  power of 4); a power of 4 is 4^k with k = 0, 1, 2, ....
* Only part (i) of the conjecture is formalized; parts (ii)-(iv) are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a279612

/-- The condition in the name of A279612 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  (∃ k : ℕ, (x : ℤ) + 2 * (y : ℤ) - 2 * (z : ℤ) = 4 ^ k) ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A279612: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A279612. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      (∃ k m : ℕ, m ∈ ({1, 2, 3, 6, 7, 8, 12, 15, 27, 31, 47, 72, 76, 92, 111, 127} : Finset ℕ) ∧ n = 16 ^ k * m))) := by
  sorry

end OMA.S_oeis_a279612
