import Mathlib

/-!
# A352636: Number of ways to write n as a^2 + 3*b^2 + c^4 + 2*d^4 + a*b*c*d, where a,b,c,d are nonnegative integers.

Source: https://oeis.org/A352636
Credit: @ceejcake

Conjecture (OEIS A352636): `a(n) > 0` except for `n = 46`.

Formalization notes:
* The sequence has offset `0` (`n : ℕ`).
* To avoid shadowing the sequence name `a`, the four nonnegative integer variables are named
  `w, x, y, z : ℕ`, counting ordered 4-tuples `(w, x, y, z)` with
  `w ^ 2 + 3 * x ^ 2 + y ^ 4 + 2 * z ^ 4 + w * x * y * z = n`.
* Because every term is nonnegative in `ℕ`, any solution satisfies the lossless bounds:
  - `w ^ 2 ≤ n`, hence `w ≤ n.sqrt`;
  - `3 * x ^ 2 ≤ n`, hence `x ^ 2 ≤ n / 3` and `x ≤ (n / 3).sqrt`;
  - `(y ^ 2) ^ 2 = y ^ 4 ≤ n`, hence `y ≤ n.sqrt.sqrt`;
  - `2 * (z ^ 2) ^ 2 = 2 * z ^ 4 ≤ n`, hence `z ^ 4 ≤ n / 2` and `z ≤ (n / 2).sqrt.sqrt`.
* Initial values for `n = 0, 1, ..., 15`:
  `a(n) = 1, 2, 2, 3, 4, 3, 3, 2, 2, 2, 1, 1, 4, 3, 3, 2, ...`, and `a(46) = 0`.
-/

namespace OMA.S_oeis_a352636

/-- `a n` is the number of ordered 4-tuples `(w, x, y, z)` of nonnegative integers such that
`w ^ 2 + 3 * x ^ 2 + y ^ 4 + 2 * z ^ 4 + w * x * y * z = n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n.sqrt + 1) ×ˢ Finset.range ((n / 3).sqrt + 1) ×ˢ
      Finset.range (n.sqrt.sqrt + 1) ×ˢ Finset.range ((n / 2).sqrt.sqrt + 1)).filter
    fun ⟨w, x, y, z⟩ => w ^ 2 + 3 * x ^ 2 + y ^ 4 + 2 * z ^ 4 + w * x * y * z = n).card

/-- OEIS A352636 conjecture: `a n > 0` for every `n : ℕ` except `n = 46`. -/
theorem main : ∀ n : ℕ, 0 < a n ↔ n ≠ 46 := by
  sorry

end OMA.S_oeis_a352636
