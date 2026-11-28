import Mathlib

/-!
# A263998: Number of ordered ways to write n as x^2 + 2*y^2 + p*(p+d)/2, where x and y are nonnegative integers, d is 1 or -1, and p is prime

Source: https://oeis.org/A263998
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, 2015, OEIS A263998): `a(n) > 0` for all `n > 0`,
and `a(n) = 1` only for `n = 1, 2, 8`.

Formalization notes:
* The sequence has offset `1`; both parts of the conjecture are stated for `n > 0`.
* `a n` counts the 4-tuples `(x, y, p, d)` with `x, y : ℕ`, `p` prime and `d ∈ {1, -1}` such
  that `x ^ 2 + 2 * y ^ 2 + p * (p + d) / 2 = n`, computed in `ℤ`. The value `p * (p + d)`
  is always even, so the division is exact. Tuples with different `d` are counted separately
  (for example `p = 2, d = 1` and `p = 3, d = -1` both give the triangular number `3`, and they
  count as two representations), as in the OEIS Mathematica program.
* The search bounds are lossless: `p * (p + d) / 2 ≥ 1` for every prime `p`, so `x ^ 2 ≤ n`
  and `y ^ 2 ≤ n`, giving `x, y ≤ n.sqrt`; and `p * (p - 1) / 2 ≥ p - 1` for `p ≥ 2`,
  so `p ≤ n + 1`, i.e. `p < n + 2`.
* Initial values for `n = 1, ..., 12`: `a(n) = 1, 1, 3, 3, 3, 3, 4, 1, 4, 4, 3, 7`.
-/

namespace OMA.S_oeis_a263998

/-- `a n` is the number of tuples `(x, y, p, d)` with `x, y` nonnegative integers, `p` prime and
`d ∈ {1, -1}` such that `n = x ^ 2 + 2 * y ^ 2 + p * (p + d) / 2`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n.sqrt + 1) ×ˢ Finset.range (n.sqrt + 1) ×ˢ
      (Finset.range (n + 2)).filter Nat.Prime ×ˢ ({1, -1} : Finset ℤ)).filter
    fun ⟨x, y, p, d⟩ =>
      (x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2 + (p : ℤ) * ((p : ℤ) + d) / 2 = (n : ℤ)).card

/-- OEIS A263998 conjecture (Zhi-Wei Sun): `a n > 0` for every `n > 0`, and for `n > 0`,
`a n = 1` if and only if `n ∈ {1, 2, 8}`. -/
theorem main :
    (∀ n : ℕ, 0 < n → 0 < a n) ∧
      (∀ n : ℕ, 0 < n → (a n = 1 ↔ n = 1 ∨ n = 2 ∨ n = 8)) := by
  sorry

end OMA.S_oeis_a263998
