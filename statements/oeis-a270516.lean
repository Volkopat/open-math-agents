import Mathlib

/-!
# OEIS A270516: x³(x+1) + y(y+1)/2 + z(3z+2)

Source: https://oeis.org/A270516 (Zhi-Wei Sun), conjecture (i) in COMMENTS
Credit: @LEGZM

a(n) is the number of ordered ways to write n = x³(x+1) + y(y+1)/2 + z(3z+2), where x and y are
nonnegative integers and z is an integer. Conjecture (i): a(n) > 0 for all n = 0, 1, 2, …, and the
only values of n > 1428 with a(n) = 1 are 2205, 2259, 3556, 4107, 4337, 5387, 9331, 16561, 22237,
27569, 63947, 78610.
-/

namespace OMA.S_oeis_a270516

/-- The ordered representations (x, y, z) of n, with x, y ≥ 0 and z ∈ ℤ. -/
def reps (n : ℕ) : Set (ℕ × ℕ × ℤ) :=
  {t | (n : ℤ) = ((t.1 ^ 3 * (t.1 + 1) + t.2.1 * (t.2.1 + 1) / 2 : ℕ) : ℤ) + t.2.2 * (3 * t.2.2 + 2)}

/-- A270516(n): the number of such representations. -/
noncomputable def a (n : ℕ) : ℕ := (reps n).ncard

theorem main : (∀ n : ℕ, 0 < a n) ∧
    {n : ℕ | 1428 < n ∧ a n = 1} =
      {2205, 2259, 3556, 4107, 4337, 5387, 9331, 16561, 22237, 27569, 63947, 78610} := by
  sorry

end OMA.S_oeis_a270516
