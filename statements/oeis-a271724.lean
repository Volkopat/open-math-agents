import Mathlib

/-!
# A271724: Number of ordered ways to write n as w^2 + x^2 + y^2 + z^2 with w*(x+2*y+3*z) a square, where w,x,y,z are nonnegative integers with x > 0.

Source: https://oeis.org/A271724
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A271724 (Zhi-Wei Sun, Apr 13 2016), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 7, 15, 47, 151, 4^k*q (k = 0,1,2,... and q = 1, 23, 71).

Conventions:
* The sequence has offset 1 (data 1, 3, 2, 1, 4, 4, 1, 3, 4, 6, 4, 2, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with x > 0, w*(x+2*y+3*z) a square and n = w^2 + x^2
  + y^2 + z^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* Only part (i) of the conjecture is formalized; parts (ii) and (iii) are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a271724

/-- The condition in the name of A271724 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  0 < x ∧ IsSquare (w * (x + 2 * y + 3 * z)) ∧ w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n

/-- A271724: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A271724. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({7, 15, 47, 151} : Finset ℕ) ∨
      (∃ k m : ℕ, m ∈ ({1, 23, 71} : Finset ℕ) ∧ n = 4 ^ k * m))) := by
  sorry

end OMA.S_oeis_a271724
