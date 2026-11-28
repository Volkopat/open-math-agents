import Mathlib

/-!
# OEIS A108957: Values of n such that n - 2^k is deficient for all 1 <= 2^k < n.

Source: https://oeis.org/A108957
Credit: @unserus

OEIS: "Conjectures: a. Sequence is infinite. b. There are infinitely many consecutive pairs,
such as (5:6), (11:12), (17:18), (53:54), ..."
Both conjectures are stated below. A number `m` is deficient when `σ(m) < 2m`. The condition
ranges over all `k` with `2^k < n` (`2^k ≥ 1` always holds). The data start at `n = 2`; for
`n = 1` the condition is vacuous and `1` is not listed, so the terms are `n ≥ 2`.
-/

namespace OMA.S_oeis_a108957

/-- `m` is deficient: `σ(m) < 2m`. -/
def IsDeficient (m : ℕ) : Prop := ArithmeticFunction.sigma 1 m < 2 * m

/-- The terms of A108957: `n ≥ 2` such that `n - 2^k` is deficient whenever `2^k < n`. -/
def a108957Set : Set ℕ := {n : ℕ | 2 ≤ n ∧ ∀ k : ℕ, 2 ^ k < n → IsDeficient (n - 2 ^ k)}

/-- (a) The sequence is infinite; (b) infinitely many `n` have both `n` and `n + 1` as terms. -/
theorem main :
    a108957Set.Infinite ∧ {n : ℕ | n ∈ a108957Set ∧ n + 1 ∈ a108957Set}.Infinite := by
  sorry

end OMA.S_oeis_a108957
