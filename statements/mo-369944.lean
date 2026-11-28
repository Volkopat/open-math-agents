import Mathlib

/-!
# MathOverflow 369944

Source: https://mathoverflow.net/questions/369944
-/

namespace OMA.S_mo_369944

open Set

theorem main : ∃ (K : Type) (top : TopologicalSpace K) (compact : @CompactSpace K top),
    letI := top
    letI := compact
    ∃ (M : Submodule ℝ C(K,ℝ)) (L : M →L[ℝ] ℝ),
      (∀ f : M, (∀ x, 0 ≤ f.val x) → 0 ≤ L f) ∧
      ¬ ∃ E : C(K,ℝ) →ₗ[ℝ] ℝ,
        (∀ f : C(K,ℝ), (∀ x, 0 ≤ f x) → 0 ≤ E f) ∧
        ∀ f : M, E f.val = L f := by
  sorry

end OMA.S_mo_369944
