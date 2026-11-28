import Mathlib

/-!
# A227345: partitions into distinct parts by size of boundary

Source: https://oeis.org/A227345
Credit: @Lenqth

A227345 is the triangle counting partitions of `n` into distinct parts by the size of their
boundary. The boundary size of a partition is the number of parts `p` that do not have two
neighbours, i.e. such that not both `p - 1` and `p + 1` are parts. A partition into distinct parts
is a finite set of positive integers; it is a partition of `n` when its elements sum to `n`.

Formalizes the conjecture in the comments of A227345 (P. Devlin, Jul 13 2013): there exists a
partition of `n` into distinct parts with boundary size `k` if and only if `0 < k^2 * 3/4 ≤ n`.
Stated for `n ≥ 1` and `k ≥ 1` (the triangle's range), where `0 < k^2 * 3/4` is automatic and
`k^2 * 3/4 ≤ n` is `3 k^2 ≤ 4 n`.
-/

namespace OMA.S_oeis_a227345

/-- The boundary size of a set of parts: parts `p` such that not both `p - 1` and `p + 1` are parts. -/
def boundarySize (S : Finset ℕ) : ℕ :=
  (S.filter fun p => ¬ (p - 1 ∈ S ∧ p + 1 ∈ S)).card

/-- A partition of `n` into distinct parts with boundary size `k` exists iff `3 k^2 ≤ 4 n`. -/
theorem main : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    ((∃ S : Finset ℕ, (∀ p ∈ S, 0 < p) ∧ ∑ p ∈ S, p = n ∧ boundarySize S = k) ↔ 3 * k ^ 2 ≤ 4 * n) := by
  sorry

end OMA.S_oeis_a227345
