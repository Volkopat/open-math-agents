import OMAStatements.S_mo_336099
import Mathlib.Algebra.Order.Star.Real

/-! Retains the fedja counterexample, formalized by @etaubman (#21342 companion)
and @Solfanbtc (#26666). Uses the standard outer-product positivity theorem. -/

open Matrix
open scoped BigOperators Matrix

private def a1 : Fin 4 → ℝ := ![1, 1, 0, 0]
private def a2 : Fin 4 → ℝ := ![0, 0, 1, 1]
private def b1 : Fin 4 → ℝ := ![1, 0, 1, 0]
private def b2 : Fin 4 → ℝ := ![0, 1, 0, 1]
private def vecV : Fin 4 → ℝ := ![1, -1, -1, 1]

private def rank1 (a : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => a i * a j

private lemma rank1_posSemidef (a : Fin 4 → ℝ) : (rank1 a).PosSemidef := by
  convert Matrix.posSemidef_vecMulVec_self_star a using 1
  ext i j
  simp [rank1, Matrix.vecMulVec]

private def matA : Matrix (Fin 4) (Fin 4) ℝ := rank1 a1 + rank1 a2
private def matB : Matrix (Fin 4) (Fin 4) ℝ := rank1 b1 + rank1 b2

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_336099.main) := by
  intro h
  have hA_psd : matA.PosSemidef := (rank1_posSemidef a1).add (rank1_posSemidef a2)
  have hB_psd : matB.PosSemidef := (rank1_posSemidef b1).add (rank1_posSemidef b2)
  have hA_nn : ∀ i j, 0 ≤ matA i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [matA, rank1, a1, a2]
  have hB_nn : ∀ i j, 0 ≤ matB i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [matB, rank1, b1, b2]
  have hA_diag : ∀ i, matA i i = 1 := by
    intro i
    fin_cases i <;> simp [matA, rank1, a1, a2]
  have hB_diag : ∀ i, matB i i = 1 := by
    intro i
    fin_cases i <;> simp [matB, rank1, b1, b2]
  have hC := h 4 (by norm_num) matA matB hA_psd hB_psd hA_nn hB_nn hA_diag hB_diag
  have hv : 0 ≤ star vecV ⬝ᵥ (OMA.S_mo_336099.hadamardL2 matA matB) *ᵥ vecV :=
    hC.dotProduct_mulVec_nonneg vecV
  have hval : star vecV ⬝ᵥ (OMA.S_mo_336099.hadamardL2 matA matB) *ᵥ vecV =
      4 * Real.sqrt 2 - 8 := by
    simp [dotProduct, mulVec, Fin.sum_univ_four, OMA.S_mo_336099.hadamardL2,
      matA, matB, rank1, a1, a2, b1, b2, vecV]
    norm_num
    ring
  rw [hval] at hv
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith
