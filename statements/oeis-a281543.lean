import Mathlib

/-!
# A281543: Number of partitions n = x + y with y >= x > 0 such that x^2 + y^2 or (x^2 + y^2)/2 is prime.

Source: https://oeis.org/A281543
Credit: @ceejcake

Conjecture (OEIS A281543): `a(n) > 0` for all `n > 1`.

Formalization notes:
* The sequence has offset `1` (`n ≥ 1`).
* Partitions `n = x + y` with `y ≥ x > 0` are represented as pairs `(x, y)` in
  `Finset.Icc 1 n ×ˢ Finset.Icc 1 n` satisfying `x ≤ y ∧ x + y = n`.
* Because natural-number division truncates, `(x^2 + y^2)/2 is prime` is guarded explicitly by
  evenness: `2 ∣ x ^ 2 + y ^ 2 ∧ ((x ^ 2 + y ^ 2) / 2).Prime`.
* Initial values for `n = 1, 2, ..., 16`:
  `a(n) = 0, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 1, 4, 3, ...`.
-/

namespace OMA.S_oeis_a281543

/-- `a n` is the number of partitions `n = x + y` with `0 < x ≤ y` such that `x ^ 2 + y ^ 2` or
`(x ^ 2 + y ^ 2) / 2` (when `x ^ 2 + y ^ 2` is even) is prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun ⟨x, y⟩ =>
    x ≤ y ∧ x + y = n ∧
      ((x ^ 2 + y ^ 2).Prime ∨ (2 ∣ x ^ 2 + y ^ 2 ∧ ((x ^ 2 + y ^ 2) / 2).Prime))).card

/-- OEIS A281543 conjecture: `a n > 0` for all `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a281543
