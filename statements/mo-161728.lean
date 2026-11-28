import Mathlib

/-!
# MathOverflow 161728

Source: https://mathoverflow.net/questions/161728
-/

namespace OMA.S_mo_161728

open Finset Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise

abbrev RealMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

def RowStochastic {d : ℕ} (M : RealMatrix d) : Prop :=
  (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1)

theorem main : ∀ (d : ℕ) (α : ℝ), 0 < α → α < 1 →
    ∀ (M : RealMatrix d) (seq : ℕ → RealMatrix d), RowStochastic M →
      (∀ n, RowStochastic (seq n)) →
      (∀ n, ‖seq n - M‖ ≤ α^n) →
      Tendsto (fun n => ‖seq n^n - M^n‖) atTop (𝓝 0) := by
  sorry

end OMA.S_mo_161728
