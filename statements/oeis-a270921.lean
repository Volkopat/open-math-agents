import Mathlib

/-!
# A270921: Number of ordered ways to write n as x*(3x+2) + y*(5y+1)/2 - z^4, where x and y are integers, and z is a nonnegative integer with z^4 <= n.

Source: https://oeis.org/A270921
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A270921 (Zhi-Wei Sun, Mar 25 2016): a(n) > 0 for all n
> 0, and a(n) = 1 only for n = 0, 5, 6, 12, 13, 14, 112, 193, 194, 200, 242, 333, 345, 376, 492,
528, 550, 551, 613, 797, 1178, 1195, 1222, 1663, 3380, 3635, 6508, 8755, 9132, 12434, 20087.

Conventions:
* The sequence has offset 0 (data 1, 2, 3, 3, 2, 1, 1, 3, 3, 3, 4, 3, ...). `a n` is the number of
  triples (x, y, z) with x, y integers, z a natural number with z^4 <= n, and n = x*(3x+2) +
  y*(5y+1)/2 - z^4, exactly as in the OEIS name.
* Integer variables range over `ℤ`; the equation and the side conditions involving them are stated
  in `ℤ`, with the natural variables and n cast.
* The division by 2 is integer division, which is exact because y*(5y+1) is always even.
* The positivity part is stated for n > 0 as in the entry; the only-if part is stated for every n
  >= 0 (the listed values include n = 0, where a(0) = 1).
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a270921

/-- The condition in the name of A270921 on a tuple, for a given n. -/
def P (n : ℕ) (x y : ℤ) (z : ℕ) : Prop :=
  z ^ 4 ≤ n ∧ x * (3 * x + 2) + y * (5 * y + 1) / 2 - (z : ℤ) ^ 4 = (n : ℤ)

/-- A270921: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℤ × ℤ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A270921. -/
theorem main : ∀ n : ℕ, (0 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({0, 5, 6, 12, 13, 14, 112, 193, 194, 200, 242, 333, 345, 376, 492, 528, 550, 551,
      613, 797, 1178, 1195, 1222, 1663, 3380, 3635, 6508, 8755, 9132, 12434, 20087} : Finset
      ℕ)) := by
  sorry

end OMA.S_oeis_a270921
