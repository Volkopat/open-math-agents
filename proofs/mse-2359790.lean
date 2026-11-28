import OMAStatements.S_mse_2359790
import Mathlib

open OMA.S_mse_2359790

private def tuple : Finset ℤ := {1, 7, 11, 13, 17, 19, 23}

private theorem unitOf {x y : ZMod 30} (h : x * y = 1) : IsUnit x :=
  ⟨⟨x, y, h, by simpa only [mul_comm] using h⟩, rfl⟩

private theorem bounds {x : ℤ} (hx : x ∈ tuple) : 1 ≤ x ∧ x ≤ 23 := by
  simp only [tuple, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_2359790.main) := by
  intro proposed
  have hu : ∃ n : ℤ, ∀ h ∈ tuple, IsUnit ((h + n : ℤ) : ZMod 30) := by
    refine ⟨0, ?_⟩
    intro h hh
    simp only [Int.add_zero]
    simp only [tuple, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact unitOf (y := 1) (by decide)
    · exact unitOf (y := 13) (by decide)
    · exact unitOf (y := 11) (by decide)
    · exact unitOf (y := 7) (by decide)
    · exact unitOf (y := 23) (by decide)
    · exact unitOf (y := 19) (by decide)
    · exact unitOf (y := 17) (by decide)
  have hwidth : ∀ a ∈ tuple, ∀ b ∈ tuple, |a - b| < (30 : ℤ) := by
    intro a ha b hb
    have ha' := bounds ha
    have hb' := bounds hb
    exact abs_lt.mpr ⟨by omega, by omega⟩
  have hadmissible := (proposed tuple 30 ⟨5, by decide⟩ hwidth).mp hu
  obtain ⟨r, hr⟩ := hadmissible 7 (by decide)
  have cover : ∀ r : ZMod 7, ∃ h ∈ tuple, (h : ZMod 7) = r := by decide
  obtain ⟨h, hh, he⟩ := cover r
  exact hr h hh he