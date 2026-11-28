import Mathlib

/-!
# Only finitely many values of the symmetric functions of 1/1, 1/2, …, 1/n are 2-adic integers (?)

Source: https://mathoverflow.net/questions/263236
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For integers `n ≥ k ≥ 1` let
  `H(n, k) = ∑_{1 ≤ i_1 < ⋯ < i_k ≤ n} 1 / (i_1 ⋯ i_k)`,
the `k`-th elementary symmetric function of `1/1, 1/2, …, 1/n`.
Question: is it true that `H(n, k)` is a `2`-adic integer only for finitely many `n` and `k`?

Conventions:
* `H n k` sums `∏_{i ∈ S} 1/i` over the `k`-element subsets `S` of `{1, …, n}` (`Finset.Icc 1 n`),
  as a rational number;
* a rational `q` is a `2`-adic integer iff `0 ≤ padicValRat 2 q`; this is unambiguous here since
  `H n k > 0` for `n ≥ k ≥ 1` (Mathlib sets `padicValRat 2 0 = 0`, but `0` never occurs);
* the statement asserts that the set of pairs `(n, k)` with `n ≥ k ≥ 1` and `H(n, k)` a `2`-adic
  integer is finite (the affirmative answer to the question). It contains `(1, 1)`, so it is not
  empty.
-/

namespace OMA.S_mo_263236

/-- `H n k`: the `k`-th elementary symmetric function of `1/1, 1/2, …, 1/n`. -/
def H (n k : ℕ) : ℚ :=
  ∑ S ∈ (Finset.Icc 1 n).powersetCard k, ∏ i ∈ S, (1 / (i : ℚ))

/-- Only finitely many `H(n, k)` with `n ≥ k ≥ 1` are `2`-adic integers. -/
theorem main :
    {p : ℕ × ℕ | 1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ 0 ≤ padicValRat 2 (H p.1 p.2)}.Finite := by
  sorry

end OMA.S_mo_263236
