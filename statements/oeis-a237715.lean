import Mathlib

/-!
# A237715: Number of ordered ways to write n = p + q (q > 0) with p, prime(p) - p + 1 and prime(prime(q)) - prime(q) + 1 all prime.

Source: https://oeis.org/A237715
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, 2014, stated in the OEIS entry): `a(n) > 0` for all `n > 2`, and
`a(n) = 1` only for `n = 3`. Both parts are formalized, as a conjunction.

Formalization notes:
* The sequence has offset `1`; `a` is defined on all of `ℕ` (with `a 0 = 0`), and the
  statement only quantifies over `n ≥ 1`.
* `prime k` is the `k`-th prime with the OEIS convention `prime(1) = 2`, i.e.
  `Nat.nth Nat.Prime (k - 1)`. It is only applied to `k ≥ 1` here (`p` is prime and `q > 0`).
* `a n` counts the `p` with `0 ≤ p ≤ n` such that `p` is prime, `q = n - p > 0`, and
  `prime(p) - p + 1` and `prime(prime(q)) - prime(q) + 1` are prime. Each ordered pair
  `(p, q)` with `p + q = n` is determined by `p`, and `p ≤ n` is forced, so
  `Finset.range (n + 1)` loses no solutions. The truncated subtractions are exact, since
  `prime k ≥ k` for every `k ≥ 1`.
* Initial values for `n = 1, ..., 16`:
  `a(n) = 0, 0, 1, 2, 2, 3, 2, 3, 4, 2, 3, 2, 2, 4, 2, 5, ...`; `a(3) = 1` via `3 = 2 + 1`.
-/

namespace OMA.S_oeis_a237715

/-- The `k`-th prime, with `prime 1 = 2` (OEIS convention, A000040). -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- `a n` is the number of ordered ways to write `n = p + q` with `q > 0` such that `p`,
`prime(p) - p + 1` and `prime(prime(q)) - prime(q) + 1` are all prime (OEIS A237715). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun p =>
    p.Prime ∧ 0 < n - p ∧ (prime p - p + 1).Prime ∧
      (prime (prime (n - p)) - prime (n - p) + 1).Prime).card

/-- OEIS A237715 conjecture (Zhi-Wei Sun): `a n > 0` for every `n > 2`, and for `n ≥ 1`,
`a n = 1` only when `n = 3`. -/
theorem main : (∀ n : ℕ, 2 < n → 0 < a n) ∧ (∀ n : ℕ, 1 ≤ n → a n = 1 → n = 3) := by
  sorry

end OMA.S_oeis_a237715
