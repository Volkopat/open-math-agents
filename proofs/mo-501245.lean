import OMAStatements.S_mo_501245

/-!
The calculation uses the block Schur-complement determinant and inverse formulas.
Each leading characteristic pencil is invertible over ℝ(X) because the
characteristic polynomial is monic. Thus the computation applies to singular
and noncommuting off-diagonal blocks. Fred Hucht's comment on the source
question refers to the recurrence of D. K. Salkuyeh, *Applied Mathematics
and Computation* 176 (2006), pp. 442–444.

Source: https://mathoverflow.net/questions/501245
-/

namespace OMA.S_mo_501245
open Matrix Polynomial

private lemma pencil_det {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    (pencil M).det = algebraMap ℝ[X] K M.charpoly :=
  ((algebraMap ℝ[X] K).map_det M.charmatrix).symm

private lemma pencil_unit {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    IsUnit (pencil M) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, pencil_det]
  intro h
  apply M.charpoly_monic.ne_zero
  apply IsFractionRing.injective ℝ[X] K
  simpa using h

private def corner {k : ℕ} : (n : ℕ) → Matrix (index k n) (index k n) K → Matrix (Fin k) (Fin k) K
  | 0, M => M
  | _+1, M => M.toBlocks₂₂

private lemma border_map {k : ℕ} (B : Matrix (Fin k) (Fin k) ℝ) (n : ℕ) :
    (border B n).map constant = border (B.map constant) n := by
  cases n with
  | zero => rfl
  | succ n =>
    ext (i | i) j
    · exact map_zero constant
    · rfl

private lemma pencil_succ {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) (n : ℕ) :
    pencil (tridiagonal A B (n+1)) = fromBlocks (pencil (tridiagonal A B n))
      (-(border (B.map constant) n)) (-(border (B.map constant) n).transpose) (pencil A) := by
  unfold pencil
  rw [tridiagonal, charmatrix_fromBlocks, fromBlocks_map, ← border_map]
  congr 1
  · ext i j; simp [Matrix.map_apply, constant]
  · ext i j; simp [Matrix.map_apply, constant]

private lemma contracted {k : ℕ} (B : Matrix (Fin k) (Fin k) K) (n : ℕ)
    (M : Matrix (index k n) (index k n) K) :
    (border B n).transpose * M * border B n = B.transpose * corner n M * B := by
  cases n with
  | zero => rfl
  | succ n =>
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    simp only [border, corner, transpose_fromRows, transpose_zero, fromCols_mul_fromBlocks,
      Matrix.zero_mul, zero_add, fromCols_mul_fromRows, Matrix.mul_zero]

private lemma schur {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K) (D : Matrix n n K)
    (hA : IsUnit A) (hM : IsUnit (fromBlocks A B C D)) :
    IsUnit (D-C*A⁻¹*B) ∧ (fromBlocks A B C D).det = A.det*(D-C*A⁻¹*B).det ∧
      (fromBlocks A B C D)⁻¹.toBlocks₂₂ = (D-C*A⁻¹*B)⁻¹ := by
  let _ := hA.invertible
  let _ := hM.invertible
  let _ := invertibleOfFromBlocks₁₁Invertible A B C D
  have h := invOf_fromBlocks₁₁_eq A B C D
  have he := congrArg Matrix.toBlocks₂₂ h
  simpa only [invOf_eq_nonsing_inv, toBlocks_fromBlocks₂₂] using
    And.intro (isUnit_of_invertible (D-C*⅟A*B)) (And.intro (det_fromBlocks₁₁ A B C D) he)

end OMA.S_mo_501245
namespace OMA.S_mo_501245
open Matrix

private lemma pivots_result {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) (n : ℕ) :
    IsUnit (pivot A B n) ∧
    (pencil (tridiagonal A B n)).det = ∏ j ∈ Finset.range (n+1), (pivot A B j).det ∧
    corner n (pencil (tridiagonal A B n))⁻¹ = (pivot A B n)⁻¹ := by
  induction n with
  | zero =>
    refine ⟨pencil_unit A,?_,rfl⟩
    simp [tridiagonal, pivot]
  | succ n ih =>
    let M := pencil (tridiagonal A B n)
    let U := border (B.map constant) n
    let D := pencil A
    have hblock : pencil (tridiagonal A B (n+1)) = fromBlocks M (-U) (-U.transpose) D :=
      pencil_succ A B n
    have hb : IsUnit (fromBlocks M (-U) (-U.transpose) D) :=
      hblock ▸ pencil_unit (tridiagonal A B (n+1))
    obtain ⟨hu,hdet,hinv⟩ := schur M (-U) (-U.transpose) D (pencil_unit _) hb
    have hs : D - (-U.transpose)*M⁻¹*(-U) = pivot A B (n+1) := by
      simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
      rw [show U.transpose * M⁻¹ * U = _ from contracted (B.map constant) n M⁻¹]
      rw [show corner n M⁻¹ = _ from ih.2.2]
      rfl
    rw [hs] at hu hdet hinv
    refine ⟨hu,?_,?_⟩
    · rw [hblock, hdet, Finset.prod_range_succ, ← ih.2.1]
    · rw [hblock]
      exact hinv

end OMA.S_mo_501245

open OMA.S_mo_501245 in
theorem OMA.solution : type_of% @OMA.S_mo_501245.main := by
  intro k _ A B _ n
  obtain ⟨hu,h,_⟩ := pivots_result A B n
  exact ⟨isUnit_iff_ne_zero.mp ((pivot A B n).isUnit_iff_isUnit_det.mp hu), (pencil_det (tridiagonal A B n)).symm.trans h⟩
