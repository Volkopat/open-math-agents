import Mathlib

/-!
# A303998: Number of ways to write 2*n+1 as p + 2^k + binomial(2*m,m), where p is a prime, and k and m are positive integers.

Source: https://oeis.org/A303998
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, May 2018, in the comments of A303998): `a(n) > 0` for all `n > 2`.

Formalization notes:
* The sequence has offset `1`; `a 0` is not part of the sequence and plays no role in the
  statement (which only concerns `n > 2`).
* `a n` counts triples `(p, k, m)` with `p` prime and `k, m ≥ 1` such that
  `2 * n + 1 = p + 2 ^ k + binomial(2 * m, m)`; the equation is stated additively in `ℕ`, so no
  subtraction is involved.
* The bounds are lossless: `p ≤ 2 * n + 1`, so `p < 2 * n + 2`; and since `p ≥ 2` and
  `binomial(2 * m, m) ≥ 2`, we get `2 * k ≤ 2 ^ k ≤ 2 * n - 3`, so `k ≤ n`; likewise
  `2 * m ≤ binomial(2 * m, m) ≤ 2 * n - 3`, so `m ≤ n`.
* Initial values for `n = 1, ..., 20`:
  `a(n) = 0, 0, 1, 2, 3, 4, 4, 5, 3, 6, 5, 6, 8, 7, 5, 7, 7, 6, 8, 11, ...`
-/

namespace OMA.S_oeis_a303998

/-- `a n` is the number of triples `(p, k, m)` with `p` prime and `k, m` positive integers such
that `2 * n + 1 = p + 2 ^ k + binomial(2 * m, m)`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 2) ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun ⟨p, k, m⟩ =>
    p.Prime ∧ p + 2 ^ k + (2 * m).choose m = 2 * n + 1).card

/-- OEIS A303998 conjecture (Zhi-Wei Sun): `a n > 0` for all `n > 2`. -/
theorem main : ∀ n : ℕ, 2 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a303998
