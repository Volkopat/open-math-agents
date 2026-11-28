import Mathlib

/-!
# A392982: Run lengths of consecutive increases of prime(n)/n where prime(n) is the n-th prime

Source: https://oeis.org/A392982
Credit: @gblacher2

Conjecture (stated in A392982): for every positive integer k there exists m with a(m) = k.

The sequence: split r(1), r(2), r(3), ... with r(n) = prime(n)/n into maximal runs of
consecutive increases; a(1), a(2), ... are the lengths of these runs. From the examples of the
source: r(1) = 2 > r(2) = 1.5, so the first run is {r(1)} and a(1) = 1; then
r(2) < r(3) < r(4) < r(5) = 2.2 > r(6), so a(2) = 4; then r(6) < r(7) > r(8), so a(3) = 2.
Equivalently, a(n) = A079418(n) - A079418(n-1) (formula of the source).

Formalization notes:
* `prime(n)` (1-indexed, prime(1) = 2) is `Nat.nth Nat.Prime (n - 1)`; `r n` is a rational number.
* "There exists m with a(m) = k" says that some maximal run has length exactly k: a run starts at
  index m when m = 1 or r(m-1) ≥ r(m), it has k - 1 consecutive increases
  r(m) < r(m+1) < ... < r(m+k-1), and it ends because r(m+k) ≤ r(m+k-1).
  (If a run never ended it would not be a term of the sequence, which is why the end is required.)
* Check of the reading: these runs reproduce the 93 data terms of A392982.
-/

namespace OMA.S_oeis_a392982

/-- `r n = prime(n) / n`, where `prime(n)` is the `n`-th prime (`prime(1) = 2`). -/
noncomputable def r (n : ℕ) : ℚ :=
  (Nat.nth Nat.Prime (n - 1) : ℚ) / n

/-- The terms `r(m), ..., r(m+k-1)` form a maximal run of consecutive increases of length `k`,
i.e. one of the terms of A392982 equals `k`. -/
def IsMaximalRun (m k : ℕ) : Prop :=
  1 ≤ m ∧ (m = 1 ∨ r m ≤ r (m - 1)) ∧
    (∀ i : ℕ, m ≤ i → i + 1 < m + k → r i < r (i + 1)) ∧ r (m + k) ≤ r (m + k - 1)

/-- The conjecture of A392982: every positive integer `k` is the length of some maximal run of
consecutive increases of `prime(n)/n`, i.e. occurs as a term of A392982. -/
theorem main : ∀ k : ℕ, 0 < k → ∃ m : ℕ, IsMaximalRun m k := by
  sorry

end OMA.S_oeis_a392982
