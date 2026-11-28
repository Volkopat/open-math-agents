import OMAStatements.S_mo_58275
import Mathlib

open scoped BigOperators
open OMA.S_mo_58275

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_58275.main) := by
  intro h
  let P : Matrix (Fin 3) (Fin 3) ℝ :=
    !![1 / 3, 1 / 3, 1 / 3; 1 / 4, 1 / 4, 1 / 2; 1 / 4, 1 / 4, 1 / 2]
  let f : Fin 3 → ℝ := ![1, -1, 0]
  have hp (i j : Fin 3) : 0 < P i j := by
    fin_cases i <;> fin_cases j <;> norm_num [P, Matrix.cons_val]
  have hs : rowStochastic P := by
    refine ⟨fun i j => (hp i j).le, ?_⟩
    intro i
    fin_cases i <;> norm_num [P, Fin.sum_univ_succ, Matrix.cons_val]
  have hi : irreducible P := fun i j => ⟨1, by decide, by simpa using hp i j⟩
  have ha : aperiodic P := by
    intro i d hd
    exact Nat.dvd_one.mp (hd 1 (by decide) (by simpa using hp i i))
  have hf : f ≠ 0 := by
    intro he
    have hz := congrFun he 0
    norm_num [f] at hz
  have he (i : Fin 3) : (∑ j, P i j * f j) = 0 * f i := by
    fin_cases i <;> norm_num [P, f, Fin.sum_univ_succ, Matrix.cons_val]
  have hm := h 3 P hs hi ha f 0 hf he 0 (show 1 ≤ 2 by decide)
  norm_num [variance, P, f, pow_two, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.cons_val] at hm