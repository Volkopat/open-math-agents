import Mathlib

/-!
# A101349: Numbers of cubes between prime(n) and prime(n+1).

Source: https://oeis.org/A101349
Credit: @gblacher2

Conjecture (comment section of A101349, Pierre Colmant, Oct 19 2026):
"a(n) <= 1 for all n if and only if there is a prime between k^3 and (k+1)^3 for every
k >= 1, which is an open conjecture. It has been verified by computation for
k^3 <= 1.649*10^40 (Johnston, Sorenson, Thomas and Webster), so a(n) <= 1 whenever
prime(n+1) <= 1.6*10^40; analytically it is known only for k >= exp(exp(32.537))
(Cully-Hugill)."

The statement below is the conjecture in the form it takes for this sequence,
a(n) <= 1 for all n, which the comment states is equivalent to the open conjecture that there
is a prime between k^3 and (k+1)^3 for every k >= 1.

The sequence has offset 1: 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, ... (a(4) = 1 counts the cube 8
between prime(4) = 7 and prime(5) = 11).

Modelling choices:
* `prime n` is the `n`-th prime for `n ≥ 1`, i.e. `Nat.nth Nat.Prime (n - 1)`, so
  `prime 1 = 2`.
* A cube is `k ^ 3` for a natural number `k`; distinct `k` give distinct cubes, so `a n`
  counts the `k` with `prime n < k ^ 3 < prime (n + 1)`. This matches the formula of the
  entry, a(n) = A048766(prime(n+1)-1) - A048766(prime(n)), where A048766(m) is the number of
  positive cubes at most m. Whether "between" is strict does not matter: a cube is never prime.
* The conjecture concerns all indices of the sequence, `n ≥ 1`.
-/

namespace OMA.S_oeis_a101349

/-- The `n`-th prime, for `n ≥ 1` (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A101349(n): the number of cubes strictly between `prime n` and `prime (n + 1)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {k : ℕ | prime n < k ^ 3 ∧ k ^ 3 < prime (n + 1)}.ncard

/-- The conjecture: a(n) ≤ 1 for all n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≤ 1 := by
  sorry

end OMA.S_oeis_a101349
