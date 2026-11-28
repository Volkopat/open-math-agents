import OMAStatements.S_mo_361272
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
A three-dimensional counterexample to the equality between PSD-squared and
doubly nonnegative matrices. The witness is the Gram matrix of the explicit
nonnegative real matrix `factor`, so it is even completely positive. A PSD
complex entrywise square root would have diagonal 1 and a zero (0,1) entry.
Its determinant would then be -1/3, independently of its complex phases.
-/

namespace OMA.S_mo_361272

open scoped ComplexOrder Matrix

private noncomputable def witness : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 2 / 3; 0, 1, 2 / 3; 2 / 3, 2 / 3, 1]

private noncomputable def factor : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, 1, 0; 2 / 3, 2 / 3, 1 / 3]

private theorem witness_factor : witness = factor * factorᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witness, factor, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, map_ofNat]

private theorem witness_psd : witness.PosSemidef := by
  rw [witness_factor]
  exact Matrix.posSemidef_self_mul_conjTranspose factor

private theorem witness_nonnegative :
    ∀ i j, (witness i j).im = 0 ∧ 0 ≤ (witness i j).re := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [witness]

private theorem no_root (X : Matrix (Fin 3) (Fin 3) ℂ) (hX : X.PosSemidef)
    (h : ∀ i j, X i j * star (X i j) = witness i j) : False := by
  have hdiag : ∀ i, X i i = 1 := by
    intro i
    have ht : witness i i = 1 := by fin_cases i <;> norm_num [witness]
    have hs := h i i
    rw [ht, hX.isHermitian.apply i i] at hs
    rcases mul_self_eq_one_iff.mp hs with hp | hm
    · exact hp
    · have hn : 0 ≤ X i i := hX.diag_nonneg
      rw [hm] at hn
      norm_num [Complex.nonneg_iff] at hn
  have h01 : X 0 1 = 0 := by
    have hz : X 0 1 * star (X 0 1) = 0 := by simpa [witness] using h 0 1
    rcases mul_eq_zero.mp hz with hleft | hright
    · exact hleft
    · simpa using hright
  have h10 : X 1 0 = 0 := by
    simpa only [h01, star_zero] using (hX.isHermitian.apply 1 0).symm
  have h20 : X 2 0 = star (X 0 2) := (hX.isHermitian.apply 2 0).symm
  have h21 : X 2 1 = star (X 1 2) := (hX.isHermitian.apply 2 1).symm
  have h02 : X 0 2 * star (X 0 2) = (2 / 3 : ℂ) := by simpa [witness] using h 0 2
  have h12 : X 1 2 * star (X 1 2) = (2 / 3 : ℂ) := by simpa [witness] using h 1 2
  have hd : X.det = (-1 / 3 : ℂ) := by
    rw [Matrix.det_fin_three, hdiag 0, hdiag 1, hdiag 2, h01, h10, h20, h21]
    simp only [zero_mul, one_mul, mul_zero, mul_one, add_zero, sub_zero]
    rw [h02, h12]
    norm_num
  have hdpos := hX.det_nonneg
  rw [hd] at hdpos
  norm_num [Complex.le_def, Complex.div_re, Complex.div_im] at hdpos


end OMA.S_mo_361272

open OMA.S_mo_361272 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_361272.main) := by
  intro h
  have hw : witness ∈ psdSquared 3 := by
    rw [h 3]
    exact ⟨witness_psd, witness_nonnegative⟩
  obtain ⟨X, hX, hEq⟩ := hw
  exact no_root X hX fun i j => (congrFun (congrFun hEq i) j).symm
