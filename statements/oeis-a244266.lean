import Mathlib

/-!
# A244266: Positive integers n such that all those prime(n+i) + prime(n+j) (i,j = 0..7) are squarefree.

Source: https://oeis.org/A244266
Credit: @K0-3A

The entry (by Zhi-Wei Sun, Jun 24 2014) records the conjecture:

  For any integer `m > 0`, there are infinitely many positive integers `n` such that all those
  `prime(n+i) + prime(n+j)` (`i, j = 0, ..., m`) are squarefree.

The sequence itself is the case `m = 7`.

Conventions.
* `prime k` is the `k`-th prime with OEIS indexing, `prime 1 = 2` (A000040). Mathlib's
  `Nat.nth Nat.Prime` is indexed from `0`, so `prime k = Nat.nth Nat.Prime (k - 1)`; `n` ranges over
  positive integers, so `n + i - 1` never truncates.
* `i` and `j` range independently over `0, ..., m`, as the comment says, so the pairs with `i = j`
  (the sums `2 * prime (n + i)`) are included. The entry's Mathematica program only tests pairs with
  `i < j`. The two readings differ only at `n = 1` (where `2 + 2 = 4` is not squarefree): for
  `n ≥ 2` every `prime (n + i)` is odd, so `2 * prime (n + i)` is squarefree. Whether infinitely many
  `n` qualify is therefore the same under both readings.
* The program's extra filter (all eight primes in the same class mod 4) does not change the set: a
  prime `≡ 1` and a prime `≡ 3 (mod 4)` sum to a multiple of `4`.
-/

namespace OMA.S_oeis_a244266

/-- `prime k`: the `k`-th prime, with `prime 1 = 2` (OEIS A000040). -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- Zhi-Wei Sun's conjecture in OEIS A244266: for every `m > 0` there are infinitely many positive
integers `n` such that `prime (n + i) + prime (n + j)` is squarefree for all `i, j ∈ {0, ..., m}`. -/
theorem main :
    ∀ m : ℕ, 0 < m →
      {n : ℕ | 0 < n ∧ ∀ i ≤ m, ∀ j ≤ m, Squarefree (prime (n + i) + prime (n + j))}.Infinite := by
  sorry

end OMA.S_oeis_a244266
