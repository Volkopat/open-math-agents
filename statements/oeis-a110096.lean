import Mathlib

/-!
# A110096: Least positive integer which, when added to each of 2^1, ..., 2^n, yields all primes; or 0 if none exists.

Source: https://oeis.org/A110096
Credit: @tczyzycki

Entry A110096 (Joseph L. Pe, offset 1) defines `a(n)` as the least positive integer `k` such that
`k + 2^1, ..., k + 2^n` are all prime, or `0` if no such `k` exists. Charles R Greathouse IV
remarks that Dickson's conjecture implies `a(n) > 0` for all `n ≥ 1`. We state the unconditional
open conjecture `∀ n ≥ 1, 0 < a n` (equivalently, for every `n ≥ 1`, there exists `k > 0` such
that `k + 2^i` is prime for all `1 ≤ i ≤ n`).
-/

namespace OMA.S_oeis_a110096

/-- `IsValid n k` holds if `k > 0` and `k + 2^i` is prime for all `i ∈ {1, ..., n}`. -/
def IsValid (n k : ℕ) : Prop :=
  0 < k ∧ ∀ i ∈ Finset.Icc 1 n, (k + 2 ^ i).Prime

/-- OEIS A110096: the least positive integer `k` such that `k + 2^1, ..., k + 2^n` are all prime,
or `0` if none exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  open Classical in
  if h : ∃ k : ℕ, IsValid n k then Nat.find h else 0

theorem main : ∀ n : ℕ, 1 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a110096
