import Mathlib

/-!
# A005250: Record gaps between primes.

Source: https://oeis.org/A005250

Conjecture (Alexei Kourbatov, Aug 05 2017): `a(n) = O(n^2)`; specifically, `a(n) ≤ n^2`, where
`a(n)` is the `n`-th record gap between consecutive primes. The sequence has offset 1 and begins
`a(1) = 1`, `a(2) = 2`, `a(3) = 4`, `a(4) = 6`, `a(5) = 8`, `a(6) = 14`, …

This file states the specific form `a(n) ≤ n^2` for every `n ≥ 1`, which implies the `O(n^2)` form.
The entry's second conjecture (the number of maximal gaps below the `k`-th prime is about
`2 * log k`) is a heuristic estimate with no stated error term, so it is not stated here.

Conventions, as in the merged statement of A053695 (differences between record prime gaps):
- A gap is `prime(k+1) - prime(k)` (not `prime(k+1) - prime(k) - 1`), with
  `prime k = Nat.nth Nat.Prime k`, so `prime 0 = 2` and `gap 0 = 1`.
- A gap `gap k` is a record when it is larger than every earlier gap `gap i`, `i < k`.
  Record gaps increase strictly with `k`, so enumerating the set of record values in increasing
  order with `Nat.nth` lists A005250 in order. `Nat.nth` counts from 0, so
  `a n = Nat.nth _ (n - 1)` restores the offset 1: `a 1 = 1`, `a 2 = 2`, `a 3 = 4`, …
-/

namespace OMA.S_oeis_a005250

/-- The gap `prime(k+1) - prime(k)` after the `k`-th prime (0-indexed: `prime 0 = 2`). -/
noncomputable def gap (k : ℕ) : ℕ := Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k

/-- `gap k` is a record: it exceeds every earlier gap. -/
def IsRecord (k : ℕ) : Prop := ∀ i < k, gap i < gap k

/-- OEIS A005250 with its offset 1: `a n` is the `n`-th record gap between primes, for `n ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun g => ∃ k, IsRecord k ∧ gap k = g) (n - 1)

/-- Kourbatov's conjecture: the `n`-th record gap between primes is at most `n^2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≤ n ^ 2 := by
  sorry

end OMA.S_oeis_a005250
