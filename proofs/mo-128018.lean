import OMAStatements.S_mo_128018
import Mathlib

open Polynomial OMA.S_mo_128018 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_128018.main) := fun h => by
  have e : integerImage (C 2 * X) = C 2 * X := by simp [integerImage, C_ofNat]
  obtain ⟨-, -, d, -, -, hd, -⟩ := h (C 2 * X) (C 2 * X) X X (e ▸ ⟨monic_X, dvd_mul_left _ _, dvd_mul_left _ _, fun _ h _ => (isUnit_C.2 (by norm_num)).dvd_mul_left.1 h⟩) ⟨1, one_pos, by simp [integerImage], fun _ h _ => h⟩ (1/2) ⟨1, by simp [complexValue]⟩ ⟨1, by simp [complexValue]⟩
  have := congrArg (2 * ·) hd
  norm_num [complexValue] at this
  norm_cast at this
  omega
