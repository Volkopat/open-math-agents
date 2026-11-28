import Mathlib

/-!
# A092940: a(n) = largest prime p such that 2*prime(n) - p is prime.

Source: https://oeis.org/A092940
Credit: @ceejcake

Conjecture (OEIS A092940): `a(n) = prime(n)` only for `n = 1` and `2`.

Formalization notes:
* `prime n` is the `n`-th prime with 1-based OEIS offset (`prime 1 = 2`, `prime 2 = 3`, ...),
  defined as `Nat.nth Nat.Prime (n - 1)` for `n ≥ 1`.
* Any prime `p` such that `2 * prime n - p` is prime (in `ℕ`) must satisfy `p < 2 * prime n`
  (since `p ≥ 2 * prime n` gives `2 * prime n - p = 0`, which is not prime), so searching over
  `Finset.range (2 * prime n)` captures every qualifying prime without loss.
* For every `n ≥ 1`, `prime n` itself satisfies `prime n < 2 * prime n` and
  `2 * prime n - prime n = prime n` is prime, so the filtered finset is nonempty and its
  `.sup id` is the exact maximum prime `p` with `2 * prime n - p` prime
  (satisfying `prime n ≤ a n < 2 * prime n`).
* Initial values for `n = 1, 2, 3, 4, 5, 6, 7, 8, ...`:
  `a(n) = 2, 3, 7, 11, 19, 23, 31, 31, 43, 53, 59, 71, 79, 83, 89, 103, 113, 109, ...`.
-/

namespace OMA.S_oeis_a092940

/-- The `n`-th prime under 1-based OEIS indexing (`prime 1 = 2`, `prime 2 = 3`, ...). -/
noncomputable def prime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- `a n` is the largest prime `p` such that `2 * prime n - p` is also prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * prime n)).filter (fun p => p.Prime ∧ (2 * prime n - p).Prime)).sup id

/-- OEIS A092940 conjecture: `a n = prime n` holds for `n ≥ 1` if and only if `n = 1` or `n = 2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = prime n ↔ n = 1 ∨ n = 2) := by
  sorry

end OMA.S_oeis_a092940
