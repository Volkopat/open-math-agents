import Mathlib

/-!
# A262944: Number of ordered pairs (x,y) with x >= 0 and y > 0 such that n - x^4 - y*(y+1)/2 is a square or a pentagonal number.

Source: https://oeis.org/A262944
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A262944 (Zhi-Wei Sun, Oct 05 2015), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 1, 9, 63, 69, 489, 714, 1089.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 2, 2, 3, 4, 3, 1, 3, 5, 3, ...). `a n` is the number of
  pairs (x, y) of natural numbers with y > 0 such that n - x^4 - y*(y+1)/2 is a square or a
  pentagonal number, exactly as in the OEIS name.
* A square is k^2 and a pentagonal number is k*(3k-1)/2 with k = 0, 1, 2, ... (A000326: 0, 1, 5,
  12, ...); `n - x^4 - y*(y+1)/2 is a square or a pentagonal number` is written without
  subtraction as an equation for n. The divisions by 2 are exact, and at k = 0 the truncated 3k -
  1 is multiplied by 0.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a262944

/-- The condition in the name of A262944 on a tuple, for a given n. -/
def P (n : ℕ) (x y : ℕ) : Prop :=
  0 < y ∧
  ∃ k : ℕ, x ^ 4 + y * (y + 1) / 2 + k ^ 2 = n ∨ x ^ 4 + y * (y + 1) / 2 + k * (3 * k - 1) / 2 = n

/-- A262944: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A262944. -/
theorem main : ∀ n : ℕ, 0 < n → ((0 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({1, 9, 63, 69, 489, 714, 1089} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a262944
