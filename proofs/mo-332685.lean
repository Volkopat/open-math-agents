import OMAStatements.S_mo_332685
import Mathlib

open Polynomial OMA.S_mo_332685

private noncomputable def e : Biv ℚ := X + C (X - 1)
private noncomputable def p : Biv ℚ := C X * X
private def grid (i : Fin 2) : ℚ := (i : ℕ)

private theorem grid_injective : Function.Injective grid := by
  intro i j hij
  apply Fin.ext
  change ((i.val : ℕ) : ℚ) = ((j.val : ℕ) : ℚ) at hij
  exact_mod_cast hij

private theorem swap_e : swap e = e := by
  simp only [swap, e, coe_eval₂RingHom, eval₂_add, eval₂_X, eval₂_C,
    coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  rw [map_sub, map_one]
  ring

private theorem swap_p : swap p = p := by
  simp only [swap, p, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_X, coe_mapRingHom, map_X]
  exact mul_comm _ _

private theorem outside : ¬ e ∣ p := by
  let ev : Biv ℚ →+* ℚ := (evalRingHom (-1)).comp (mapRingHom (evalRingHom 2))
  have he : ev e = 0 := by norm_num [ev, e]
  have hp : ev p = -2 := by norm_num [ev, p]
  intro hd
  have hm := map_dvd ev hd
  rw [he, hp] at hm
  norm_num at hm

theorem OMA.solution : type_of% @OMA.S_mo_332685.main := by
  have he : e.natDegree = 1 := natDegree_X_add_C (X - 1 : ℚ[X])
  have hp : p.natDegree = 1 := by simp [p, natDegree_mul]
  have hse : degreeX e = 1 := by simpa only [degreeX, swap_e] using he
  have hsp : degreeX p = 1 := by simpa only [degreeX, swap_p] using hp
  refine ⟨ℚ, inferInstance, 2, 2, grid, grid, e, p, by decide, by decide,
    grid_injective, grid_injective, ?_, ?_, ?_, ?_, ?_, ?_, ?_, outside⟩
  · intro h
    simp [h] at he
  · intro h
    simp [h] at hp
  · omega
  · omega
  · norm_num [hsp, hp]
  · intro i
    fin_cases i <;> simp [atX, grid, e, p]
  · intro i
    fin_cases i <;> simp [atY, grid, e, p]