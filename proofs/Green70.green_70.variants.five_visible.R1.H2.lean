import OMAReductions.R_Green70_green_70_variants_five_visible_R1
import Mathlib

/-! A single point of P is a collinear subset of size one. -/

open scoped Finset

theorem OMA.solution : OMA.R_Green70_green_70_variants_five_visible_R1.H2 := by
  intro P hP
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hP
  exact ⟨{p}, Finset.singleton_subset_iff.mpr hp, Finset.card_singleton p,
    by simpa using collinear_singleton ℝ p⟩
