import Mathlib

/-!
# A275409: Number of ordered ways to write n as 2*w^2 + x^2 + y^2 + z^2 with w + x + 2*y + 4*z a square, where w,x,y,z are nonnegative integers.

Source: https://oeis.org/A275409
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A275409 (Zhi-Wei Sun):
(i) a(n) > 0 except for n = 3, 10, and a(n) = 1 only for n = 0, 2, 7, 8, 9, 12, 14, 15, 22, 23,
24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183.

Conventions:
* The sequence has offset 0 (data 1, 2, 1, 0, 2, 2, 2, 1, 1, 1, 0, 3, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with w + x + 2*y + 4*z a square and n = 2*w^2 + x^2 +
  y^2 + z^2, exactly as in the OEIS name.
* A square means the square of an integer (0 included), rendered as `IsSquare` on natural numbers.
* Only part (i) of the conjecture is formalized; parts (ii) to (iv) concern other conditions.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every natural number n other than the exceptions 3, 10 named
  in the entry (that a(n) = 0 there is a finite computation and is not part of the statement).
* The second part is rendered literally as an only-if, for every natural number n: a(n) = 1
  implies that n is one of the listed values.
-/

namespace OMA.S_oeis_a275409

/-- A275409: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ × ℕ | IsSquare (x.1 + x.2.1 + 2 * x.2.2.1 + 4 * x.2.2.2) ∧
    2 * x.1 ^ 2 + x.2.1 ^ 2 + x.2.2.1 ^ 2 + x.2.2.2 ^ 2 = n}

/-- The conjecture of Sun recorded in A275409. -/
theorem main : ∀ n : ℕ,
    (n ≠ 10 → n ≠ 3 → 0 < a n) ∧ (a n = 1 →
      n ∈ ({0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111,
      183} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a275409
