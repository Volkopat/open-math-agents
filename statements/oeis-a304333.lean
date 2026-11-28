import Mathlib

/-!
# A304333: Number of positive integers k such that n - L(k) is a positive squarefree number, where L(k) denotes the k-th Lucas number A000204(k).

Source: https://oeis.org/A304333
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, May 2018, in the comments of A304333): `a(n) > 0` for all `n > 1`.

Formalization notes:
* The sequence has offset `1`; `a 0` is not part of the sequence and plays no role in the
  statement (which only concerns `n > 1`).
* Lucas numbers (A000032): `L(0) = 2`, `L(1) = 1`, `L(k + 2) = L(k + 1) + L(k)`. Only `k ≥ 1`
  is counted (A000204 starts `1, 3, 4, 7, ...`), so `L(0) = 2` is never used.
* `n - L(k)` is required to be positive explicitly (`lucas k < n`), so truncated subtraction in
  `ℕ` plays no role; `Squarefree` is Mathlib's notion on `ℕ`.
* The range `k ≤ n` is lossless: `L(k) ≥ k` for every `k ≥ 1`, so `L(k) < n` forces `k < n`.
* Initial values for `n = 1, ..., 20`:
  `a(n) = 0, 1, 1, 2, 2, 3, 2, 3, 3, 3, 2, 3, 3, 5, 2, 3, 4, 5, 2, 4, ...`
-/

namespace OMA.S_oeis_a304333

/-- The Lucas numbers: `L 0 = 2`, `L 1 = 1`, `L (k + 2) = L (k + 1) + L k`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | k + 2 => lucas (k + 1) + lucas k

/-- `a n` is the number of positive integers `k` such that `n - L(k)` is a positive squarefree
number. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter fun k => lucas k < n ∧ Squarefree (n - lucas k)).card

/-- OEIS A304333 conjecture (Zhi-Wei Sun): `a n > 0` for all `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a304333
