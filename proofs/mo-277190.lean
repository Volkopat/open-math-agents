import OMAStatements.S_mo_277190

namespace OMA.S_mo_277190

open Matrix Polynomial
open scoped Polynomial ComplexOrder

private lemma offdiag_charpoly {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (fromBlocks 0 A B 0).charpoly = (A*B).charpoly.comp (X^2) := by
  apply mul_right_cancel₀ (pow_ne_zero n (X_ne_zero : (X : ℂ[X])≠0))
  apply Polynomial.funext
  intro t
  let S := Matrix.scalar (Fin n) t
  have h₁ : Matrix.scalar (Fin n ⊕ Fin n) t - fromBlocks 0 A B 0 = fromBlocks S (-A) (-B) S := by
    ext (i|i) (j|j) <;> simp [S,Matrix.scalar_apply,diagonal_apply,fromBlocks]
  have h₂ : fromBlocks S (-A) (-B) S * fromBlocks S 0 B 1 =
      fromBlocks (Matrix.scalar (Fin n) (t^2) - A*B) (-A) 0 S := by
    rw [fromBlocks_multiply]
    congr 1
    · simp [S,pow_two,map_mul,sub_eq_add_neg]
    · simp
    · simp only [neg_mul]
      have hs : B*S=S*B := by ext i j; simp [S,Matrix.scalar_apply,diagonal_mul,mul_diagonal,mul_comm]
      rw [hs,neg_add_cancel]
    · simp
  have hdet := congrArg Matrix.det h₂
  rw [det_mul,det_fromBlocks_zero₁₂,det_one,mul_one,det_fromBlocks_zero₂₁] at hdet
  simp only [eval_mul,eval_pow,eval_X,eval_comp,eval_charpoly,h₁]
  simpa [S,Matrix.scalar_apply] using hdet

private lemma dilation_factor {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (dilation M).charpoly = ∏ i, ((X - C (singular M i : ℂ)) * (X + C (singular M i : ℂ))) := by
  let h := posSemidef_self_mul_conjTranspose M
  rw [dilation,offdiag_charpoly,h.isHermitian.charpoly_eq,Polynomial.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  have hs : (singular M i : ℂ)^2 = (h.isHermitian.eigenvalues i : ℂ) := by
    exact_mod_cast Real.sq_sqrt (h.eigenvalues_nonneg i)
  simp only [sub_comp,X_comp,C_comp]
  change X^2 - C (h.isHermitian.eigenvalues i : ℂ) = _
  rw [← hs,map_pow]; ring

end OMA.S_mo_277190
namespace OMA.S_mo_277190
open Polynomial Matrix
open scoped Polynomial

private lemma jordan_example : ∃ M : Matrix (Fin 2) (Fin 2) ℂ,
    M.charpoly = (X-1)^2 ∧ (dilation M).charpoly.Separable := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![1,1;0,1]
  have hG : M*M.conjTranspose = !![2,1;1,1] := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [M,Matrix.mul_apply,Fin.sum_univ_two]
  refine ⟨M,?_,?_⟩
  · rw [charpoly_fin_two]
    norm_num [M,trace_fin_two,det_fin_two]
    simp only [C_ofNat]; ring
  · have hq : (dilation M).charpoly = X^4-3*X^2+1 := by
      rw [dilation,offdiag_charpoly,hG,charpoly_fin_two]
      norm_num [trace_fin_two,det_fin_two,add_comp,sub_comp,mul_comp,pow_comp]
      simp only [C_ofNat]; ring
    rw [hq,separable_def]
    refine ⟨C (1/10 : ℂ) * (10-12*X^2), C (1/10 : ℂ) * (3*X^3-7*X),?_⟩
    have hd : derivative (X^4-3*X^2+1 : ℂ[X]) = 4*X^3-6*X := by
      simp [derivative_pow]; simp only [C_ofNat]; ring
    rw [hd]
    calc
      _ = C (1/10:ℂ)*10 := by ring
      _ = C ((1/10:ℂ)*10) := by rw [map_mul,C_ofNat]
      _ = 1 := by norm_num

end OMA.S_mo_277190

open OMA.S_mo_277190 in
theorem OMA.solution : type_of% @OMA.S_mo_277190.main :=
  ⟨fun _ M => dilation_factor M, jordan_example⟩
