import OMAStatements.S_mo_424348
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_424348.main) := fun h => by
  obtain ⟨p, q, hpq, hx⟩ := h 3 3 (by norm_num) (by norm_num) (fun i k => ((![1, -1, 2, -2, 3, -3] : Fin 6 → ℤ) i : ℝ) ^ (k : ℕ)) (fun e => by
    refine (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.vandermonde fun i => ((![1, -1, 2, -2, 3, -3] : Fin 6 → ℤ) (e i) : ℝ))).2 ?_
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
    exact (Int.cast_injective.comp (by decide : Function.Injective ![(1 : ℤ), -1, 2, -2, 3, -3])).comp e.injective) ![![-27, 0, 3], ![-32, 0, 8], 0] ![0, 0, 1, 1, 2, 2] ![1, 1, 2, 2, 0, 0] (by decide) (fun i => by fin_cases i <;> simp [Fin.sum_univ_three] <;> norm_num)
  have := congrFun hx 0
  fin_cases p <;> fin_cases q <;> first | exact hpq rfl | norm_num at this
