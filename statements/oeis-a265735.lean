import Mathlib

/-!
# A265735: Integers in the interval [Pi*k - 1/k, Pi*k + 1/k] for some k > 0

Source: https://oeis.org/A265735
Credit: @xor2k

Conjecture (OEIS A265735): the sequence is infinite.

Conventions: the sequence is the set of integers `m` for which there exists a positive
integer `k` such that `m` lies in the closed interval
`[pi * k - 1 / k, pi * k + 1 / k]`. Thus `k` ranges over positive natural numbers,
encoded by `1 ≤ k`, and the endpoint condition is written as
`|pi * k - m| ≤ 1 / k`. The offset of the OEIS sequence is 1.

Remark: this statement coincides with statements/oeis-a265739.lean up to the parameters
(and the role of the quantifiers): A265739 asserts that infinitely many `k` admit an
integer `m` in the interval, while A265735 asserts that infinitely many integers `m`
occur in the interval for some positive `k`. The interval and the bound `1 / k` are the
same in both statements.
-/

namespace OMA.S_oeis_a265735

/-- `m` is one of the integers lying in `[pi * k - 1 / k, pi * k + 1 / k]` for some
positive integer `k`. -/
def IsTerm (m : ℤ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ |Real.pi * (k : ℝ) - (m : ℝ)| ≤ 1 / (k : ℝ)

/-- The sequence of integers in `[pi * k - 1 / k, pi * k + 1 / k]`, for some `k > 0`,
is infinite. -/
theorem main : Set.Infinite {m : ℤ | IsTerm m} := by
  sorry

end OMA.S_oeis_a265735
