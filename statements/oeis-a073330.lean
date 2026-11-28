import Mathlib

/-!
# A073330: Let c(1)=n and c(k+1)=floor(c(k)/Pi) if c(k) is even, or c(k+1)=floor(Pi*c(k)) otherwise; sequence gives the smallest value a(n) such that c(a(n))=0.

Source: https://oeis.org/A073330
Credit: @eltociear

Let `c(1) = n` and `c(k+1) = ⌊c(k)/π⌋` if `c(k)` is even, `⌊π c(k)⌋` if `c(k)` is odd. `a(n)`
(offset 1) is the least `k` with `c(k) = 0` (`a(1) = 7`: `1, 3, 9, 28, 8, 2, 0`). The entry's
formula section records:

  Conjecture: sequence always exists (a(123456789)=61, a(2^30)=70) and there is a constant
  C=2.8... such that sum(k=1, n, a(k)) is asymptotic to C*n*Log(n)

`main` is the conjunction of the two claims: (1) for every `n ≥ 1` some iterate reaches `0`;
(2) there is a constant `C` whose decimal expansion begins `2.8` (read as `2.8 ≤ C < 2.9`) with
`∑_{k=1}^n a(k) ~ C n log n`. `a n` is `sInf` of the admissible indices (`0` if none, which (1)
rules out). `log` is the natural logarithm, as in the entry's PARI-style `Log`.

Remark for reviewers (not part of the statement): a direct computation of the partial sums gives
`∑ a(k) / (n log n) ≈ 3.06, 3.00, 3.07, 2.89` at `n = 10^4, 10^5, 2·10^5, 4·10^5`, so the
numerical value of `C` is not settled by the data; the statement records the entry's `2.8...`.
-/

namespace OMA.S_oeis_a073330

/-- One step: `⌊c/π⌋` if `c` is even, `⌊π·c⌋` if `c` is odd. -/
noncomputable def step (c : ℕ) : ℕ :=
  if Even c then ⌊(c : ℝ) / Real.pi⌋₊ else ⌊Real.pi * (c : ℝ)⌋₊

/-- OEIS: the least `k ≥ 1` with `c(k) = 0`, where `c(1) = n` and `c(k+1) = step (c(k))`
(`0` if there is none). -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ step^[k - 1] n = 0}

/-- The conjecture in OEIS A073330. -/
theorem main : (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, step^[k] n = 0) ∧
    ∃ C : ℝ, 2.8 ≤ C ∧ C < 2.9 ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun N : ℕ => ((∑ k ∈ Finset.Icc 1 N, a k : ℕ) : ℝ)) (fun N : ℕ => C * N * Real.log N) := by
  sorry

end OMA.S_oeis_a073330
