import Mathlib

/-!
# A270594: Number of ordered ways to write n as the sum of a triangular number, a positive square and the square of a generalized pentagonal number (A001318).

Source: https://oeis.org/A270594
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A270594 (Zhi-Wei Sun, Mar 19 2016), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 1, 3, 21, 24, 48, 90, 138, 213, 283, 462, 468, 567, 573,
1998, 2068, 2488, 2687, 5208, 5547, 5638, 6093, 6492, 6548, 6717, 7538, 7731, 8522, 14763, 16222,
17143, 24958, 26148.

Conventions:
* The sequence has offset 1 (data 1, 2, 1, 2, 4, 2, 2, 4, 2, 3, 5, 2, ...). `a n` is the number of
  triples (x, y, z) with x a natural number, y a positive integer and z an integer such that n =
  x*(x+1)/2 + y^2 + (z*(3z-1)/2)^2, i.e. the number of ordered ways to write n as the sum of a
  triangular number, a positive square and the square of a generalized pentagonal number, as in
  the OEIS name.
* The triangular numbers are x*(x+1)/2 with x = 0, 1, 2, ... (0 included) and the generalized
  pentagonal numbers (A001318) are z*(3z-1)/2 with z an integer; distinct x (resp. distinct
  integers z) give distinct triangular (resp. generalized pentagonal) numbers, so counting the
  parameters (x, y, z) counts the ordered ways. This reproduces the OEIS data and examples (e.g.
  a(24) = 1 uses the generalized pentagonal number 0).
* The equation is stated in `ℤ` with x, y, n cast; both integer divisions by 2 are exact.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a270594

/-- The condition in the name of A270594 on a tuple, for a given n. -/
def P (n : ℕ) (x y : ℕ) (z : ℤ) : Prop :=
  0 < y ∧ (x : ℤ) * (x + 1) / 2 + (y : ℤ) ^ 2 + (z * (3 * z - 1) / 2) ^ 2 = n

/-- A270594: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℤ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A270594. -/
theorem main : ∀ n : ℕ, 0 < n → ((0 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({1, 3, 21, 24, 48, 90, 138, 213, 283, 462, 468, 567, 573, 1998, 2068, 2488, 2687,
        5208, 5547, 5638, 6093, 6492, 6548, 6717, 7538, 7731, 8522, 14763, 16222, 17143,
        24958, 26148} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a270594
