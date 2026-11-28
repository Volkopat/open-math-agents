import OMAStatements.S_mo_381970

/-!
Positive-coefficient counterexample to Charles Cao's finite-average assertion:
https://mathoverflow.net/questions/381970

Short submission form of RobVanProd's earlier complete Lean certificate:
https://github.com/RobVanProd/open-math-agents/blob/fbd78191ef578394239eb3055f0611c377f3b190/certificates/BlockMatrixAverageCounterexample.lean

The diagonal coefficients are 3 and all edge coefficients are 1. The identity
and swap determinants are 400 and 320; their uniform average is 360, not 400.
-/

open OMA.S_mo_381970 Matrix
open scoped BigOperators

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_381970.main) := by
  intro h
  let A (σ : Equiv.Perm (Fin 2)) :=
    cyclicBlockMatrix 3 2 (fun _ => 3) (fun _ => 1) σ
  have identity_det : (A 1).det = 400 := by
    let B : Matrix (Fin 6) (Fin 6) ℝ :=
      !![3,0,1,0,1,0; 0,3,0,1,0,1; 1,0,3,0,1,0;
         0,1,0,3,0,1; 1,0,1,0,3,0; 0,1,0,1,0,3]
    have he : A 1 = B.submatrix finProdFinEquiv finProdFinEquiv := by
      ext ⟨i,a⟩ ⟨j,b⟩
      fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
        norm_num [A, B, cyclicBlockMatrix, Matrix.submatrix, finProdFinEquiv]
    rw [he, Matrix.det_submatrix_equiv_self]
    dsimp [B]
    eval_det
  have swap_det : (A (Equiv.swap 0 1)).det = 320 := by
    let B : Matrix (Fin 6) (Fin 6) ℝ :=
      !![3,0,1,0,0,1; 0,3,0,1,1,0; 1,0,3,0,1,0;
         0,1,0,3,0,1; 0,1,1,0,3,0; 1,0,0,1,0,3]
    have he : A (Equiv.swap 0 1) = B.submatrix finProdFinEquiv finProdFinEquiv := by
      ext ⟨i,a⟩ ⟨j,b⟩
      fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
        norm_num [A, B, cyclicBlockMatrix, Matrix.submatrix, finProdFinEquiv,
          Equiv.Perm.permMatrix, PEquiv.toMatrix, Equiv.swap_apply_def]
    rw [he, Matrix.det_submatrix_equiv_self]
    dsimp [B]
    eval_det
  have hperms : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by decide
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  have hcard : Fintype.card (Equiv.Perm (Fin 2)) = 2 := by decide
  have havg := h 3 2 (by decide) (by decide) (by decide) (fun _ => 3) (fun _ => 1)
  change (∑ σ : Equiv.Perm (Fin 2), (A σ).det) /
    (Fintype.card (Equiv.Perm (Fin 2)) : ℝ) = (A 1).det at havg
  rw [hperms, Finset.sum_pair hne, identity_det, swap_det, hcard] at havg
  norm_num at havg
