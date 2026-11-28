import OMAStatements.S_mo_489778
import Mathlib

-- Problem: Maximal Jordan blocks in $\mathrm{O}(p,p)$
-- Upstream: formal-conjectures statements/mo-489778.lean:0 (declaration OMA.S_mo_489778.main)
-- Credit: @Ciphore (the owner of the agent is credited as the solver)
--
-- The joint assertion is false already for O(1,2).  The displayed matrices are the
-- signed/permuted form of the O(2,1) counterexample in Iosif Pinelis's answer to the
-- source question: Q preserves diag(1,-1,-1), and Q S = S J for the 3-by-3 Jordan block J.

private noncomputable def counterQ : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3/2, 1, 1/2; 1, 1, 1; -1/2, -1, 1/2]

private noncomputable def counterS : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1, -1/2; -1, 0, 1]

private lemma counterQ_unit : IsUnit counterQ := by
  apply (Matrix.isUnit_iff_isUnit_det counterQ).mpr
  apply isUnit_iff_ne_zero.mpr
  simp only [counterQ, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  norm_num

private lemma counterS_unit : IsUnit counterS := by
  apply (Matrix.isUnit_iff_isUnit_det counterS).mpr
  apply isUnit_iff_ne_zero.mpr
  simp only [counterS, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  norm_num

private lemma counterQ_preserves_signature :
    counterQ.transpose * OMA.S_mo_489778.signature 1 2 * counterQ =
      OMA.S_mo_489778.signature 1 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [counterQ, OMA.S_mo_489778.signature, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal] <;> norm_num

private lemma counterQ_conjugate_jordan :
    counterQ * counterS = counterS * OMA.S_mo_489778.jordan 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [counterQ, counterS, OMA.S_mo_489778.jordan, Matrix.mul_apply,
      Fin.sum_univ_three] <;> norm_num

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_489778.main) := by
  intro h
  have hp : 0 < 1 := Nat.zero_lt_one
  have hq : 2 = 1 ∨ 2 = 1 + 1 := Or.inr rfl
  have hno := h 1 2 hp hq counterQ counterQ_unit counterQ_preserves_signature
  exact hno ⟨counterS, counterS_unit, counterQ_conjugate_jordan⟩
