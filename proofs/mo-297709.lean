import OMAStatements.S_mo_297709
import Mathlib

open Set Matrix
open scoped ComplexOrder

open OMA.S_mo_297709

private noncomputable def rankOneVector : Fin 2 → ℂ :=
  fun i => (↑(if i = 0 then (1 : ℝ) else 1/2) : ℂ)

private theorem star_rankOne_apply (i : Fin 2) : star (rankOneVector i) = rankOneVector i := by
  simp [rankOneVector]

private noncomputable def fractionalExtreme : Matrix (Fin 2) (Fin 2) ℂ :=
  vecMulVec rankOneVector (star rankOneVector)

private noncomputable def nullVector : Fin 2 → ℂ :=
  fun i => if i = 0 then -1/2 else 1

private theorem fractional_matrix_zero : fractionalExtreme *ᵥ nullVector = 0 := by
  rw [fractionalExtreme,vecMulVec_mulVec]
  have hZero : star rankOneVector ⬝ᵥ nullVector = 0 := by
    norm_num [dotProduct,Fin.sum_univ_two,Pi.star_apply,star_rankOne_apply,rankOneVector,nullVector]
  simp [hZero]

private theorem fractional_00 : fractionalExtreme 0 0 = 1 := by
  norm_num [fractionalExtreme,vecMulVec_apply,Pi.star_apply,star_rankOne_apply,rankOneVector]

private theorem fractional_01 : fractionalExtreme 0 1 = 1/2 := by
  norm_num [fractionalExtreme,vecMulVec_apply,Pi.star_apply,star_rankOne_apply,rankOneVector]

private theorem fractional_10 : fractionalExtreme 1 0 = 1/2 := by
  norm_num [fractionalExtreme,vecMulVec_apply,Pi.star_apply,star_rankOne_apply,rankOneVector]

private theorem fractional_11 : fractionalExtreme 1 1 = 1/4 := by
  norm_num [fractionalExtreme,vecMulVec_apply,Pi.star_apply,star_rankOne_apply,rankOneVector]

private noncomputable def formAtNull (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  star nullVector ⬝ᵥ (A *ᵥ nullVector)

private theorem form_respects_combination (t s : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    formAtNull (t • A + s • B) = t • formAtNull A + s • formAtNull B := by
  simp only [formAtNull,add_mulVec,smul_mulVec,dotProduct_add,dotProduct_smul]

private theorem left_saturates {x y t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hTotal : t+s=1)
    (hx : x ≤ 1) (hy : y ≤ 1) (hMix : t*x+s*y=1) : x=1 := by
  have hX : 0 ≤ t*(1-x) := mul_nonneg ht.le (sub_nonneg.mpr hx)
  have hY : 0 ≤ s*(1-y) := mul_nonneg hs.le (sub_nonneg.mpr hy)
  have hz : t*(1-x) = 0 := by linarith
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ht.ne')).symm

private theorem from_kernel_and_diagonal (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef)
    (hK : A *ᵥ nullVector = 0) (h00 : A 0 0 = 1) : A = fractionalExtreme := by
  have eqRow (i : Fin 2) : A i 0 * (-1/2) + A i 1 = 0 := by
    have he := congrFun hK i
    simpa [mulVec,dotProduct,Fin.sum_univ_two,nullVector] using he
  have h01 : A 0 1 = 1/2 := by
    have he := eqRow 0
    rw [h00] at he
    linear_combination he
  have hHerm : star (A 1 0) = A 0 1 := by
    exact congrArg (fun T : Matrix (Fin 2) (Fin 2) ℂ => T 0 1) hA.isHermitian
  have h10 : A 1 0 = 1/2 := by
    rw [h01] at hHerm
    simpa [Complex.star_def] using congrArg star hHerm
  have h11 : A 1 1 = 1/4 := by
    have he := eqRow 1
    rw [h10] at he
    linear_combination he
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00.trans fractional_00.symm
  · exact h01.trans fractional_01.symm
  · exact h10.trans fractional_10.symm
  · exact h11.trans fractional_11.symm

private theorem matrix_is_extreme : fractionalExtreme ∈ (BoundedDiagonalPSD 2).extremePoints ℝ := by
  constructor
  · refine ⟨posSemidef_vecMulVec_self_star rankOneVector,?_⟩
    intro i
    fin_cases i
    · change (fractionalExtreme 0 0).re ≤ 1
      rw [fractional_00]
      norm_num
    · change (fractionalExtreme 1 1).re ≤ 1
      rw [fractional_11]
      norm_num [Complex.div_re]
  · intro A hA B hB hSeg
    obtain ⟨t,s,ht,hs,hSum,hmix⟩ := hSeg
    have hA0 : 0 ≤ formAtNull A := hA.1.dotProduct_mulVec_nonneg nullVector
    have hB0 : 0 ≤ formAtNull B := hB.1.dotProduct_mulVec_nonneg nullVector
    have hZ : formAtNull fractionalExtreme = 0 := by
      simp only [formAtNull,fractional_matrix_zero,dotProduct_zero]
    have hQ := congrArg formAtNull hmix
    rw [form_respects_combination,hZ] at hQ
    have hR := congrArg Complex.re hQ
    simp only [Complex.add_re,Complex.smul_re,smul_eq_mul,Complex.zero_re] at hR
    have hAr := (Complex.nonneg_iff.mp hA0).1
    have hBr := (Complex.nonneg_iff.mp hB0).1
    have hRa : t*(formAtNull A).re = 0 := by
      linarith [mul_nonneg ht.le hAr,mul_nonneg hs.le hBr]
    have hAc : formAtNull A = 0 := Complex.ext
      ((mul_eq_zero.mp hRa).resolve_left ht.ne') (Complex.nonneg_iff.mp hA0).2.symm
    have hK : A *ᵥ nullVector = 0 := (hA.1.dotProduct_mulVec_zero_iff nullVector).mp hAc
    have hD := congrArg (fun T : Matrix (Fin 2) (Fin 2) ℂ => (T 0 0).re) hmix
    simp only [Matrix.add_apply,Matrix.smul_apply,Complex.add_re,Complex.smul_re,smul_eq_mul,
      fractional_00,Complex.one_re] at hD
    have hDiag := left_saturates ht hs hSum (hA.2 0) (hB.2 0) hD
    have hDiagIm := (Complex.nonneg_iff.mp (hA.1.diag_nonneg (i := 0))).2.symm
    exact from_kernel_and_diagonal A hA.1 hK (Complex.ext hDiag hDiagIm)

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_297709.main) := by
  intro h
  have hNe : fractionalExtreme ≠ 0 := by
    intro he
    have h00 : fractionalExtreme 0 0 = 0 :=
      congrArg (fun T : Matrix (Fin 2) (Fin 2) ℂ => T 0 0) he
    rw [fractional_00] at h00
    exact one_ne_zero h00
  have hVal := h 2 fractionalExtreme hNe matrix_is_extreme 1
  rw [fractional_11] at hVal
  norm_num at hVal
