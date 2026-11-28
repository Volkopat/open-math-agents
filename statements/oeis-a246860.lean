import Mathlib

/-!
# OEIS A246860: Johnston's conjecture for the even moments of the trace on O(4)

Source: https://oeis.org/A246860
Credit: @yooeonwoo

Entry A246860 (offset 1): Expected value of trace(O)^(2n), where O is a 4 x 4 orthogonal matrix
randomly selected according to Haar measure.
Data (n >= 1): 1, 3, 15, 105, 903, 8778, 92235, 1023165, ...

Conjecture (Nathaniel Johnston, MathOverflow 180110; recorded by Robert Israel, Jan 17 2020):
a(n) = A000108(n) * (A000108(n) + 1) / 2, where A000108(n) is the n-th Catalan number.

Formalization notes:
* The real 4 x 4 orthogonal group O(4) is `Matrix.orthogonalGroup (Fin 4) ℝ`, endowed with its
  subspace topology from `Matrix (Fin 4) (Fin 4) ℝ` (making it a compact Hausdorff topological
  group) and its Borel sigma-algebra.
* The normalized Haar measure on O(4) is characterized uniquely as a Borel probability measure `μ`
  satisfying `MeasureTheory.Measure.IsHaarMeasure μ` and `MeasureTheory.IsProbabilityMeasure μ`.
* The expected value of `trace(O)^(2n)` is the Bochner integral `∫ O, (O.val.trace) ^ (2 * n) ∂μ`.
* `catalan n` is Mathlib's n-th Catalan number A000108(n) (`catalan 0 = 1, catalan 1 = 1,
  catalan 2 = 2, catalan 3 = 5, catalan 4 = 14, ...`).
* Following the entry's offset 1, the conjecture is stated for all natural numbers `n ≥ 1`.
-/

namespace OMA.S_oeis_a246860

open MeasureTheory

/-- Expected value of `trace(O)^(2n)` with respect to a probability Haar measure `μ` on O(4). -/
noncomputable def a [MeasurableSpace (Matrix.orthogonalGroup (Fin 4) ℝ)]
    (μ : Measure (Matrix.orthogonalGroup (Fin 4) ℝ)) (n : ℕ) : ℝ :=
  ∫ O : Matrix.orthogonalGroup (Fin 4) ℝ, (O.val.trace) ^ (2 * n) ∂μ

/-- Conjecture (Nathaniel Johnston): for `O` distributed according to normalized Haar measure on
O(4) and every `n ≥ 1`, `E[trace(O)^(2n)] = C_n * (C_n + 1) / 2`. -/
theorem main :
    ∀ [MeasurableSpace (Matrix.orthogonalGroup (Fin 4) ℝ)]
      [BorelSpace (Matrix.orthogonalGroup (Fin 4) ℝ)]
      (μ : Measure (Matrix.orthogonalGroup (Fin 4) ℝ))
      [Measure.IsHaarMeasure μ]
      [IsProbabilityMeasure μ]
      (n : ℕ), 1 ≤ n →
      a μ n = (catalan n : ℝ) * ((catalan n : ℝ) + 1) / 2 := by
  sorry

end OMA.S_oeis_a246860
