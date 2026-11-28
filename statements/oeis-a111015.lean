import Mathlib

/-!
# OEIS A111015: Primes in A002535

Source: https://oeis.org/A111015
Credit: @unserus

OEIS: "Conjecture: Starting with 1/1, there are infinitely many primes in the
numerators of fractions built according to the rule: add top and bottom to get
the new bottom, add top and 2k times bottom to get the new top, for k>=1."

Following the OEIS formula (`t(0) = b(0) = 1`, `t(i) = t(i-1) + 10*b(i-1)`,
`b(i) = t(i-1) + b(i-1)`; the sequence is the case `k = 5`), the fractions are
the unreduced pairs `(top, bottom)` produced by
`(t, b) ↦ (t + 2k * b, t + b)` from `(1, 1)`. The conjecture is that for every
`k ≥ 1` infinitely many primes occur among the tops.
-/

namespace OMA.S_oeis_a111015

/-- The pair `(top, bottom)` after `i` steps of `(t, b) ↦ (t + 2k b, t + b)`,
starting from `(1, 1)`. -/
def frac (k : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | i + 1 => ((frac k i).1 + 2 * k * (frac k i).2, (frac k i).1 + (frac k i).2)

/-- For every `k ≥ 1` the numerators contain infinitely many primes. -/
theorem main :
    ∀ k : ℕ, 1 ≤ k → {p : ℕ | p.Prime ∧ ∃ i, (frac k i).1 = p}.Infinite := by
  sorry

end OMA.S_oeis_a111015
