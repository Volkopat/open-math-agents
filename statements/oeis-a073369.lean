import Mathlib

/-!
# A073369: Let c(1)=n, e=2.71... and c(k+1)=floor(c(k)/e) if c(k) is even, c(k+1)=floor(e*c(k)) otherwise; sequence gives the smallest value a(n) such that c(a(n))=0.

Source: https://oeis.org/A073369
Credit: @eltociear

Let `c(1) = n` and `c(k+1) = ⌊c(k)/e⌋` if `c(k)` is even, `⌊e c(k)⌋` if `c(k)` is odd, where
`e = exp 1`. `a(n)` (offset 1) is the least `k` with `c(k) = 0` (`a(1) = 3`: `1, 2, 0`). The
entry's formula section records:

  Conjecture: sequence always exists and there is a constant C=2.9... such that sum(k=1, n, a(k))
  is asymptotic to C*n*Log(n). Is this constant the same as those for the sequence involving Pi
  instead of e?

`main` is the conjunction of the two claims: (1) for every `n ≥ 1` some iterate reaches `0`;
(2) there is a constant `C` whose decimal expansion begins `2.9` (read as `2.9 ≤ C < 3`) with
`∑_{k=1}^n a(k) ~ C n log n`. The closing question is not part of the conjecture. `a n` is `sInf`
of the admissible indices (`0` if none, which (1) rules out). `log` is the natural logarithm.

Remark for reviewers (not part of the statement): a direct computation of the partial sums gives
`∑ a(k) / (n log n) ≈ 2.82, 2.87, 2.92, 3.02` at `n = 10^4, 10^5, 2·10^5, 4·10^5`, so the
numerical value of `C` is not settled by the data; the statement records the entry's `2.9...`.
-/

namespace OMA.S_oeis_a073369

/-- One step: `⌊c/e⌋` if `c` is even, `⌊e·c⌋` if `c` is odd. -/
noncomputable def step (c : ℕ) : ℕ :=
  if Even c then ⌊(c : ℝ) / Real.exp 1⌋₊ else ⌊Real.exp 1 * (c : ℝ)⌋₊

/-- OEIS: the least `k ≥ 1` with `c(k) = 0`, where `c(1) = n` and `c(k+1) = step (c(k))`
(`0` if there is none). -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ step^[k - 1] n = 0}

/-- The conjecture in OEIS A073369. -/
theorem main : (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, step^[k] n = 0) ∧
    ∃ C : ℝ, 2.9 ≤ C ∧ C < 3 ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun N : ℕ => ((∑ k ∈ Finset.Icc 1 N, a k : ℕ) : ℝ)) (fun N : ℕ => C * N * Real.log N) := by
  sorry

end OMA.S_oeis_a073369
