import Mathlib

/-!
# OEIS A033282: diagonal dissections of a convex n-gon (Lang's conjecture)

Source: https://oeis.org/A033282
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`T(n, k)` is the number of diagonal dissections of a convex `n`-gon into `k + 1` regions; the entry
gives `T(n, k) = C(n-3, k) * C(n+k-1, k) / (k+1)` for `n ≥ 3`, `0 ≤ k ≤ n-3`, used here as the
definition. Lang's conjecture (2017, stated true by Copeland): the signed triangle
`t(n, k) = (-1)^k T(n+2, k-1)`, `n ≥ 1`, `1 ≤ k ≤ n`, is obtained from the reversion array A111785
by summing its entries over the partitions of `n` with exactly `k` parts. The A111785 entry for a
partition `1^s₁ 2^s₂ ⋯` of `n` with `j` parts is `(-1)^j (n+j)! / ((n+1)! ∏ sᵢ!)` (Howroyd's formula
in A111785).
-/

namespace OMA.S_oeis_a033282

/-- `T(n, k)` of A033282. -/
def T (n k : ℕ) : ℚ := ((n - 3).choose k * (n + k - 1).choose k : ℚ) / (k + 1)

/-- The A111785 entry attached to a partition `p` of `n`. -/
def rev (n : ℕ) (p : Nat.Partition n) : ℚ :=
  (-1 : ℚ) ^ p.parts.card * ((n + p.parts.card).factorial : ℚ) /
    (((n + 1).factorial : ℚ) * ∏ i ∈ p.parts.toFinset, ((p.parts.count i).factorial : ℚ))

/-- Lang's conjecture. -/
theorem main : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → k ≤ n →
    (-1 : ℚ) ^ k * T (n + 2) (k - 1) =
      ∑ p ∈ (Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.parts.card = k), rev n p := by
  sorry

end OMA.S_oeis_a033282
