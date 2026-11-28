import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Source: https://arxiv.org/html/2609.05546v2#S3 -/

open scoped BigOperators

namespace OMA.S_mo_514729

noncomputable def mass (a : ℕ → ℕ) (p : ℝ) : ℕ → ℕ → ℝ
  | 0, i => if i = 0 then p else if i = 1 then 1 - p else 0
  | n + 1, i =>
    let offset := a (n + 1) - a n
    p * (if i < a n then mass a p n i else 0) +
      (1 - p) * (if offset ≤ i ∧ i < a (n + 1) then mass a p n (i - offset) else 0)

noncomputable def entropy (a : ℕ → ℕ) (n : ℕ) (p : ℝ) : ℝ :=
  -(∑ i ∈ Finset.range (a n), mass a p n i * Real.log (mass a p n i))

theorem main :
    ∀ a : ℕ → ℕ, StrictMono a → a 0 = 2 → ∀ n : ℕ,
      ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (entropy a n) := by
  sorry

end OMA.S_mo_514729
