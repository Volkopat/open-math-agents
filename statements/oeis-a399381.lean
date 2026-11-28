import Mathlib

/-!
# A common limit for two squarefree hitting-time averages

Aidan Markey conjectures that the averages of the first `N` terms of
OEIS A399381 and A399382 converge to the same real number as `N` tends
to infinity. Both sequences start at index one.

Sources: https://oeis.org/A399381 and https://oeis.org/A399382
(OEIS Foundation, CC BY-SA 4.0).
Credit: @wtho704
-/

namespace OMA.S_oeis_a399381

open Filter
open scoped BigOperators Topology

/-- A399381 at a positive index `n`. -/
noncomputable def minusTerm (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ Squarefree (k * n - 1)}

/-- A399382 at a positive index `n`. -/
noncomputable def plusTerm (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ Squarefree (k * n + 1)}

theorem main : ∃ c : ℝ,
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, (minusTerm n : ℝ)) / (N : ℝ))
      atTop (𝓝 c) ∧
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, (plusTerm n : ℝ)) / (N : ℝ))
      atTop (𝓝 c) := by
  sorry

end OMA.S_oeis_a399381
