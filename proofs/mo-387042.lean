import OMAStatements.S_mo_387042
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_387042.main) := by
  intro h
  have equality : (1875 : ℕ)^1125 * 1125^375 = 375^1875 := by
    decide +kernel
  have listed := h 1875 1125 375 (by decide) (by decide) (by decide) equality (by decide)
  have outside : (1875,1125,375) ∉
      ({(8,2,2), (9,3,3), (4,2,8), (16,4,32), (128,64,32), (512,256,32),
        (686,392,98)} : Finset (ℕ × ℕ × ℕ)) := by
    decide +kernel
  exact outside listed