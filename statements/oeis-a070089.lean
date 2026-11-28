import Mathlib

/-!
# A070089: P(n) < P(n+1) where P(n) (A006530) is the largest prime factor of n.

Source: https://oeis.org/A070089
Credit: @my-other-github-account

Conjecture (Erdős; stated in A070089): this sequence has asymptotic density 1/2.

Formalization notes:
* `P n` is A006530, the largest prime factor of `n`, with the OEIS convention `P 1 = 1`
  (A006530(1) = 1). The value at `n = 0` (outside the sequence's range) is irrelevant.
* The sequence has offset 1, so its terms are the `n ≥ 1` with `P n < P (n + 1)`.
* Asymptotic density 1/2: `#{1 ≤ n ≤ N : P n < P (n + 1)} / N → 1/2` as `N → ∞`.
-/

namespace OMA.S_oeis_a070089

open Filter Topology

/-- A006530: the largest prime factor of `n`, with `P 1 = 1`. -/
def P (n : ℕ) : ℕ := if n = 1 then 1 else n.primeFactors.sup id

/-- Erdős's conjecture: the terms of A070089 have asymptotic density 1/2. -/
theorem main :
    Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n => P n < P (n + 1))).card : ℝ) / N)
      atTop (𝓝 (1 / 2)) := by
  sorry

end OMA.S_oeis_a070089
