import OMAStatements.S_mo_401929

-- Part 1: expand the shifted Gram matrix; D is a sum of two rank-one matrices, and for u ⊥ e,
-- D u = (Σ x · u) e, so dotting b u = a u + (Σ x · u) e with u gives a = b.
-- Part 2: explicit samples built from (1, 0) and (±3/5, ±4/5); the determinants 896/25 and 320/25
-- of the two Gram matrices differ, so the characteristic polynomials differ.

namespace OMA.MO401929
open Matrix Finset OMA.S_mo_401929

lemma rank_add_le' {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  have h1 : LinearMap.range (A.mulVecLin + B.mulVecLin) ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := LinearMap.range_add_le _ _
  exact (Submodule.finrank_mono h1).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma D_eq {T n : ℕ} (x : Fin T → Vec n) (e : Vec n) :
    gram (fun t => x t + e) - gram x =
      vecMulVec ((∑ t, x t) + (T : ℝ) • e) e + vecMulVec e (∑ t, x t) := by
  ext i j
  simp only [OMA.S_mo_401929.gram, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib, show (T : ℝ) * e i = ∑ _t : Fin T, e i by simp, add_mul, Finset.sum_mul, Finset.sum_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

noncomputable def A6 : Fin 6 → Vec 2 := ![![1, 0], ![1, 0], ![3/5, 4/5], ![3/5, -4/5], ![-3/5, 4/5], ![-3/5, 4/5]]
noncomputable def B6 : Fin 6 → Vec 2 := ![![-3/5, 4/5], ![-3/5, 4/5], ![-3/5, -4/5], ![-3/5, -4/5],
  ![-3/5, -4/5], ![-3/5, -4/5]]
noncomputable def C6 : Fin 6 → Vec 2 := ![![1, 0], ![1, 0], ![3/5, 4/5], ![3/5, 4/5], ![-3/5, -4/5], ![-3/5, -4/5]]
noncomputable def D6 : Fin 6 → Vec 2 := fun _ => ![-3/5, -4/5]

noncomputable def xs : Sample → Vec 2 := fun t => if t.1 = 0 then A6 t.2 else B6 t.2
noncomputable def ys : Sample → Vec 2 := fun t => if t.1 = 0 then C6 t.2 else D6 t.2

end OMA.MO401929

open OMA.MO401929 OMA.S_mo_401929 Matrix in
theorem OMA.solution : type_of% @OMA.S_mo_401929.main := by
  refine ⟨?_, ?_⟩
  · intro T n x e
    simp only
    refine ⟨D_eq x e, ?_, ?_⟩
    · rw [D_eq]
      have h1 := rank_vecMulVec_le ((∑ t, x t) + (T : ℝ) • e) e
      have h2 := rank_vecMulVec_le e (∑ t, x t)
      have := rank_add_le' (vecMulVec ((∑ t, x t) + (T : ℝ) • e) e) (vecMulVec e (∑ t, x t))
      omega
    · intro u hu he a b ha hb
      have hsplit : gram (fun t => x t + e) = gram x +
          (vecMulVec ((∑ t, x t) + (T : ℝ) • e) e + vecMulVec e (∑ t, x t)) := by
        rw [← D_eq]; abel
      rw [hsplit, add_mulVec, add_mulVec, ha, vecMulVec_mulVec, vecMulVec_mulVec,
        dotProduct_comm e u, he] at hb
      have hd := congrArg (fun w => w ⬝ᵥ u) hb
      simp only [MulOpposite.op_zero, zero_smul, zero_add, add_dotProduct, smul_dotProduct,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul] at hd
      rw [dotProduct_comm e u, he, zero_mul, add_zero] at hd
      have hu2 : u ⬝ᵥ u ≠ 0 := fun h => hu (dotProduct_self_eq_zero.mp h)
      exact mul_right_cancel₀ hu2 hd
  · refine ⟨xs, ys, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨i, j⟩
      fin_cases i <;> fin_cases j <;>
        simp [xs, ys, A6, B6, C6, D6, dotProduct, Fin.sum_univ_succ] <;> norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [OMA.S_mo_401929.gram, xs, A6, B6, Matrix.sum_apply, vecMulVec_apply,
          Fintype.sum_prod_type, Fin.sum_univ_succ] <;> norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [OMA.S_mo_401929.gram, ys, C6, D6, Matrix.sum_apply, vecMulVec_apply,
          Fintype.sum_prod_type, Fin.sum_univ_succ] <;> norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [OMA.S_mo_401929.gram, xs, A6, B6, Matrix.sum_apply, vecMulVec_apply,
          Fintype.sum_prod_type, Fin.sum_univ_succ] <;> norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [OMA.S_mo_401929.gram, ys, C6, D6, Matrix.sum_apply, vecMulVec_apply,
          Fintype.sum_prod_type, Fin.sum_univ_succ] <;> norm_num
    · intro h
      have hx : OMA.S_mo_401929.gram xs = !![28/5, 0; 0, 32/5] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [OMA.S_mo_401929.gram, xs, A6, B6, Matrix.sum_apply, vecMulVec_apply,
            Fintype.sum_prod_type, Fin.sum_univ_succ] <;> norm_num
      have hy : OMA.S_mo_401929.gram ys = !![28/5, 24/5; 24/5, 32/5] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [OMA.S_mo_401929.gram, ys, C6, D6, Matrix.sum_apply, vecMulVec_apply,
            Fintype.sum_prod_type, Fin.sum_univ_succ] <;> norm_num
      have hdet := congrArg (fun P => P.coeff 0) h
      try simp only at hdet
      have e1 := Matrix.det_eq_sign_charpoly_coeff (OMA.S_mo_401929.gram xs)
      have e2 := Matrix.det_eq_sign_charpoly_coeff (OMA.S_mo_401929.gram ys)
      rw [← hdet, ← e1] at e2
      rw [hx, hy, Matrix.det_fin_two_of, Matrix.det_fin_two_of] at e2
      norm_num at e2

