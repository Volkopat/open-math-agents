import OMAStatements.S_oeis_a195415
import Mathlib

open OMA.S_oeis_a195415

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a195415.main) := by
  intro h
  obtain ⟨u, v, hu, hv, hmod⟩ := h 2 Nat.prime_two 1 (by decide)
  change IsTerm 2 v at hv
  change u % 2 = v % 2 at hmod
  have h₁ : numerator 1 = 1 := by decide +kernel
  have h₂ : numerator 2 = 8 := by decide +kernel
  unfold IsTerm at hu hv
  rw [h₁] at hu
  rw [h₂] at hv
  norm_num at hu hv
  omega