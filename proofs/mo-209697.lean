import OMAStatements.S_mo_209697

/-!
Credited port of @connoranderson's complete public proof, linked from statement PR #23794
and desk DONE note #108919, pinned at:
https://github.com/connoranderson/open-math-agents/blob/3e4a4780f254c98d0a5fc286f95304f47fee0d90/proofs/mo-209697.lean
The mathematical code is retained unchanged. This is integration of prior proof work,
not a claim of a new result. The problem is Jay's; Igor Khavkine identified the
Schur/singular-value reduction, and Ben Grossmann gave the Schur-complement approach
in the linked cross-post (with small-eigenvalue discussion by Armadillo Jim).
-/

namespace OMA.S_mo_209697
open Matrix

private lemma real_bound (n : ℕ) (hn : 0<n) (B : Matrix (Fin n) (Fin n) ℝ)
    (hflat : ∀ i j, |B i j| = (Real.sqrt (2*(n:ℝ)))⁻¹) (hp : (gram B).PosDef) :
    ((2*(n:ℝ))^n)⁻¹ ≤ (gram B).det := by
  let d : ℝ := 2*(n:ℝ)
  let s := Real.sqrt d
  have hd : 0<d := by dsimp [d]; positivity
  have hs : 0<s := Real.sqrt_pos.mpr hd
  let E : Matrix (Fin n) (Fin n) ℤ := Matrix.of (fun i j => if 0≤B i j then 1 else -1)
  let φ := (Int.castRingHom ℝ).mapMatrix (m := Fin n)
  have he : φ E=s • B := by
    ext i j
    have h := hflat i j
    change |B i j|=s⁻¹ at h
    by_cases hy : 0≤B i j
    · rw [abs_of_nonneg hy] at h
      simp [φ,E,Matrix.smul_apply,h,hs.le,mul_inv_cancel₀ hs.ne']
    · rw [abs_of_neg (lt_of_not_ge hy)] at h
      have hh : B i j = -s⁻¹ := by linarith
      simp [φ,E,Matrix.smul_apply,hh,not_le.mpr hs,mul_inv_cancel₀ hs.ne']
  let D : Matrix (Fin n) (Fin n) ℤ := (2*(n:ℤ)) • 1 - E*E.transpose
  have heT : φ E.transpose = (φ E).transpose := rfl
  have hD : φ D = d • (1 - B*B.conjTranspose) := by
    dsimp only [D]
    rw [map_sub,map_mul,heT,he]
    have hdiag : φ ((2*(n:ℤ)) • (1 : Matrix (Fin n) (Fin n) ℤ)) = d • 1 := by
      rw [map_zsmul,map_one]
      ext i j
      change (2*(n:ℤ)) • ((1 : Matrix (Fin n) (Fin n) ℝ) i j) = d*((1 : Matrix (Fin n) (Fin n) ℝ) i j)
      simp [zsmul_eq_mul,d]
    rw [hdiag,smul_sub,Matrix.transpose_smul,smul_mul_assoc,mul_smul_comm,smul_smul]
    rw [show s*s=d by simpa [s,pow_two] using Real.sq_sqrt hd.le]
    rfl
  have hdet := congrArg Matrix.det hD
  rw [← (Int.castRingHom ℝ).map_det,Matrix.det_smul,Fintype.card_fin] at hdet
  have hgram : (gram B).det=(1-B*B.conjTranspose).det := det_fromBlocks_one₂₂ ..
  rw [← hgram] at hdet
  have hpos : 0<(D.det:ℝ) := hdet.trans_gt (mul_pos (pow_pos hd _) hp.det_pos)
  have hone : (1:ℝ) ≤ (D.det:ℝ) := by
    have hh : (0:ℤ)<D.det := by exact_mod_cast hpos
    exact_mod_cast (show (1:ℤ)≤D.det by omega)
  change (d^n)⁻¹ ≤ _
  rw [inv_le_iff_one_le_mul₀ (pow_pos hd _),mul_comm,← hdet]
  exact hone

end OMA.S_mo_209697
namespace OMA.S_mo_209697
open Matrix
open scoped ComplexOrder

private lemma complex_small (ε : ℝ) (hε : 0<ε) : ∃ B : Matrix (Fin 2) (Fin 2) ℂ,
    (∀ i j, ‖B i j‖ = 1/2) ∧ (gram B).PosDef ∧ (gram B).det.re < ε := by
  let u := min ε 1
  have hu : 0<u := lt_min hε zero_lt_one
  have hu₁ : u≤1 := min_le_right ..
  have huε : u≤ε := min_le_left ..
  let s := 1-u/2
  have hs : 0<s := by dsimp [s]; linarith
  have hs₁ : s<1 := by dsimp [s]; linarith
  have hsq : 0<1-s^2 := by nlinarith [mul_pos (sub_pos.mpr hs₁) (show 0<1+s by linarith)]
  let z : ℂ := ⟨s,Real.sqrt (1-s^2)⟩
  have hnorm : ‖z‖=1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; simp [z,Real.sq_sqrt hsq.le]
  have hp : z * star z = 1 := by simpa [hnorm] using Complex.mul_conj' z
  have hsum : z + star z = 2*(s:ℂ) := by apply Complex.ext <;> simp [z]; ring
  let B : Matrix (Fin 2) (Fin 2) ℂ := !![1/2,1/2;z/2,star z/2]
  let H : Matrix (Fin 2) (Fin 2) ℂ := !![1/2,-(s:ℂ)/2;-(s:ℂ)/2,1/2]
  simp only [Complex.star_def] at hp hsum
  have hH : 1-B*B.conjTranspose=H := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B,H,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.one_apply,Matrix.conjTranspose_apply,map_ofNat] <;>
      first | linear_combination -hsum/4 | linear_combination -hp/2
  have hdet : (gram B).det = ((1-s^2)/4 : ℝ) := by
    rw [gram,det_fromBlocks_one₂₂,hH,det_fin_two]
    simp [H]; ring
  have hpsd : H.PosSemidef := by
    let U : Matrix (Fin 2) (Fin 2) ℂ := !![1,1;1,-1]
    let v : Fin 2 → ℂ := ![((1-s)/4 : ℝ),((1+s)/4 : ℝ)]
    have hv : (diagonal v).PosSemidef := by
      apply PosSemidef.diagonal
      intro i; fin_cases i
      · exact Complex.zero_le_real.mpr (by linarith : 0 ≤ (1-s)/4)
      · exact Complex.zero_le_real.mpr (by linarith : 0 ≤ (1+s)/4)
    have hf : U * diagonal v * U.conjTranspose = H := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [U,v,H,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.diagonal_apply,Matrix.conjTranspose_apply] <;>
        ring
    exact hf ▸ hv.mul_mul_conjTranspose_same U
  have hg : (gram B).PosSemidef := by
    let : Invertible (1 : Matrix (Fin 2) (Fin 2) ℂ) := invertibleOne
    apply (Matrix.PosDef.fromBlocks₂₂ 1 B (Matrix.PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℂ).PosDef)).mpr
    simpa [hH] using hpsd
  refine ⟨B,?_,hg.posDef_iff_det_ne_zero.mpr ?_,?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [B,hnorm,norm_div]
  · rw [hdet]; exact_mod_cast (show (1-s^2)/4 ≠ 0 by positivity)
  · rw [hdet,Complex.ofReal_re]; dsimp [s]; nlinarith [sq_nonneg u]

end OMA.S_mo_209697
namespace OMA.S_mo_209697
open Matrix
open scoped ComplexOrder

private lemma real_eigen_bound {n : ℕ} (hn : 0<n) (B : Matrix (Fin n) (Fin n) ℝ)
    (hp : (gram B).PosDef) (hdet : ((2*(n:ℝ))^n)⁻¹ ≤ (gram B).det) (i : Fin n ⊕ Fin n) :
    ((2*(n:ℝ))^(3*n-1))⁻¹ ≤ hp.isHermitian.eigenvalues i := by
  let d := 2*(n:ℝ)
  let l := hp.isHermitian.eigenvalues
  have hd : 0<d := by dsimp [d]; positivity
  have hsum : (∑ j, l j) = d := by
    calc
      _ = (gram B).trace := hp.isHermitian.trace_eq_sum_eigenvalues.symm
      _ = _ := by
        simp [gram,Matrix.trace,Matrix.diag,Matrix.fromBlocks,Fintype.sum_sum_type,d,two_mul]
  have hle (j) : l j ≤ d := hsum ▸ Finset.single_le_sum (fun x _ => (hp.eigenvalues_pos x).le) (Finset.mem_univ j)
  have hprod : (gram B).det = ∏ j, l j := hp.isHermitian.det_eq_prod_eigenvalues
  have hleprod := Finset.prod_le_prod (s := Finset.univ.erase i) (fun j _ => (hp.eigenvalues_pos j).le)
    (fun j _ => hle j)
  have hcard : (Finset.univ.erase i).card=2*n-1 := by simp [two_mul]
  have hh : (gram B).det ≤ l i * d^(2*n-1) := by
    rw [hprod,← Finset.mul_prod_erase Finset.univ l (Finset.mem_univ i)]
    apply mul_le_mul_of_nonneg_left _ (hp.eigenvalues_pos i).le
    simpa [hcard] using hleprod
  change (d^(3*n-1))⁻¹ ≤ l i
  rw [inv_le_iff_one_le_mul₀ (pow_pos hd _),show 3*n-1=(2*n-1)+n by omega,pow_add,← mul_assoc]
  have hbase : 1 ≤ (gram B).det * d^n := (inv_le_iff_one_le_mul₀ (pow_pos hd _)).mp hdet
  exact hbase.trans (mul_le_mul_of_nonneg_right hh (pow_pos hd _).le)

private lemma complex_eigen_small (ε : ℝ) (hε : 0<ε) : ∃ B : Matrix (Fin 2) (Fin 2) ℂ,
    (∀ i j, ‖B i j‖ = 1/2) ∧ ∃ hp : (gram B).PosDef,
      (gram B).det.re < ε ∧ ∃ i, hp.isHermitian.eigenvalues i < ε := by
  obtain ⟨B,hf,hp,hdet⟩ := complex_small (min ε (ε^4)) (lt_min hε (pow_pos hε _))
  refine ⟨B,hf,hp,hdet.trans_le (min_le_left ..),?_⟩
  by_contra! hh
  have hprod := Finset.prod_le_prod (s := Finset.univ) (fun i _ => hε.le) (fun i _ => hh i)
  have hd : (gram B).det.re = ∏ i, hp.isHermitian.eigenvalues i := by
    have he := hp.isHermitian.det_eq_prod_eigenvalues
    change (gram B).det = ∏ i, ((hp.isHermitian.eigenvalues i : ℝ) : ℂ) at he
    rw [← Complex.ofReal_prod] at he
    rw [he,Complex.ofReal_re]
  rw [hd] at hdet
  exact (not_le.mpr (hdet.trans_le (min_le_right ..))) (by simpa using hprod)

end OMA.S_mo_209697

open OMA.S_mo_209697 in
theorem OMA.solution : type_of% @OMA.S_mo_209697.main := by
  refine ⟨?_,complex_eigen_small⟩
  intro n hn B hflat hp
  have h := real_bound n hn B hflat hp
  exact ⟨h,real_eigen_bound hn B hp h⟩

