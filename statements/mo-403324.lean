import Mathlib

/-!
# Is this conjecture about the binomial and beta distributions true?

Source: https://mathoverflow.net/questions/403324
Credit: @datdzrgb

The expectations are finite sums over the support of the binomial law. For
`p = 0` the expectation `a` vanishes and the quotient in the source is
undefined, so the statement uses `0 < p ≤ 1`.
-/

namespace OMA.S_mo_403324

open MeasureTheory ProbabilityTheory

noncomputable def expectedExcess (n k : ℕ) (p : Set.Icc (0 : ℝ) 1) : ℝ :=
  ∑ x ∈ Finset.range (n + 1), (binomial n p).real {x} * (↑(x - k) : ℝ)

noncomputable def expectedLogChoose (n k : ℕ) (p : Set.Icc (0 : ℝ) 1) : ℝ :=
  ∑ x ∈ Finset.range (n + 1), (binomial n p).real {x} * Real.log (x.choose (x - k))

theorem main :
    ∀ (n k : ℕ) (p : Set.Icc (0 : ℝ) 1), 1 < k → k < n → 0 < (p : ℝ) →
      let a := expectedExcess n k p
      let b := expectedLogChoose n k p
      Real.sqrt (n : ℝ) *
          (∫ t in (0 : ℝ)..(p : ℝ), Real.sqrt (cdf (betaMeasure k (↑(n - k) : ℝ)) t)) ≤
        3 * Real.sqrt (a * (p : ℝ)) * Real.exp (b / (-2 * a)) := by
  sorry

end OMA.S_mo_403324
