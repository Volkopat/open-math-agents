import OMAStatements.S_mo_331165
import Mathlib

open OMA.S_mo_331165

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_331165.main) := by
  intro h
  let ρ : Space → ℝ := fun _ => 1
  let v : Space → Space := fun _ _ => 1
  have hdiv (B : Space) (_ : B ≠ 0) (x : Space) : divField (current ρ v B) x = 0 := by
    simp [divField, coordDeriv, current, ρ, v]
  obtain ⟨a, ha⟩ := h ρ v (differentiable_const _) (by intro x; exact zero_lt_one)
    (differentiable_const _) hdiv 0
  have e := congrFun ha (0 : Fin 3)
  simp [ρ, v, grad, coordDeriv] at e