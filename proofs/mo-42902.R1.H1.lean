import OMAReductions.R_mo_42902_R1
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The Marcus–de Oliveira determinant bound in dimension three

Bebiano, Merikoski and da Providência proved the three-dimensional case
in 1987. See https://doi.org/10.1080/03081088708817750.
The mixed terms are linear in the doubly stochastic matrix of squared
moduli. The Birkhoff decomposition then gives the required convex combination.
-/

open Matrix Finset
open scoped BigOperators ComplexConjugate

namespace OMA.MarcusThree

private def complementProduct (a : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  ∏ j ∈ univ.erase i, a j

private theorem complementProduct_reindex (a : Fin 3 → ℂ) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    complementProduct (a ∘ σ) i = complementProduct a (σ i) := by
  have hmap : (univ.erase i).map σ.toEmbedding = univ.erase (σ i) := by
    rw [Finset.map_erase, Finset.map_univ_equiv]
    rfl
  rw [complementProduct, complementProduct, ← hmap, Finset.prod_map]
  rfl

private theorem det_diagonal_add_three (a : Fin 3 → ℂ) (C : Matrix (Fin 3) (Fin 3) ℂ) :
    (diagonal a + C).det =
      (∏ i, a i) + C.det +
        ∑ i, (complementProduct a i * C i i + a i * C.adjugate i i) := by
  have h₀ : (univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
  have h₁ : (univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
  have h₂ : (univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  rw [Matrix.det_fin_three (diagonal a + C), Matrix.det_fin_three C, Matrix.adjugate_fin_three]
  simp [Matrix.add_apply, Fin.prod_univ_three, Fin.sum_univ_three,
    complementProduct, h₀, h₁, h₂]
  ring

private theorem adjugate_unitary {n : Type} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℂ) (hW : star W * W = 1) :
    W.adjugate = W.det • star W := by
  calc
    W.adjugate = star W * (W * W.adjugate) := by rw [← mul_assoc, hW, one_mul]
    _ = W.det • star W := by rw [Matrix.mul_adjugate, Matrix.mul_smul, mul_one]

private theorem adjugate_conj_unitary {n : Type} [Fintype n] [DecidableEq n]
    (W : Matrix.unitaryGroup n ℂ) (C : Matrix n n ℂ) :
    ((W : Matrix n n ℂ) * C * star (W : Matrix n n ℂ)).adjugate =
      (W : Matrix n n ℂ) * C.adjugate * star (W : Matrix n n ℂ) := by
  let T : Matrix n n ℂ := W
  have ht : T * star T = 1 := Unitary.coe_mul_star_self W
  have ht' : star T * T = 1 := Unitary.coe_star_mul_self W
  have hdet : (star T).det * T.det = 1 := by rw [← Matrix.det_mul, ht', Matrix.det_one]
  have ha := adjugate_unitary T ht'
  have hb : (star T).adjugate = (star T).det • T := by
    simpa only [star_star] using adjugate_unitary (star T) (by simpa only [star_star] using ht)
  change (T * C * star T).adjugate = T * C.adjugate * star T
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, ha, hb, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hdet, one_smul, mul_assoc]

private theorem diag_conj_apply {n : Type} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℂ) (b : n → ℂ) (i : n) :
    (W * diagonal b * star W) i i = ∑ j, Complex.normSq (W i j) • b j := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal, Matrix.star_apply, Complex.star_def, Complex.real_smul,
    ← Complex.mul_conj]
  ring

private theorem unitary_normSq_doublyStochastic {n : Type} [Fintype n] [DecidableEq n]
    (W : Matrix.unitaryGroup n ℂ) :
    (Matrix.of fun i j => Complex.normSq ((W : Matrix n n ℂ) i j)) ∈ doublyStochastic ℝ n := by
  let T : Matrix n n ℂ := W
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨fun i j => Complex.normSq_nonneg (T i j), ?_, ?_⟩
  · intro i
    apply Complex.ofReal_injective
    simp only [Matrix.of_apply, Complex.ofReal_sum, Complex.ofReal_one, ← Complex.mul_conj]
    change (∑ j, T i j * conj (T i j)) = 1
    have h : T * star T = 1 := Unitary.coe_mul_star_self W
    simpa only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def, Matrix.one_apply_eq]
      using congrArg (fun C : Matrix n n ℂ => C i i) h
  · intro j
    apply Complex.ofReal_injective
    simp only [Matrix.of_apply, Complex.ofReal_sum, Complex.ofReal_one, ← Complex.mul_conj]
    have h : star T * T = 1 := Unitary.coe_star_mul_self W
    calc
      (∑ i, T i j * conj (T i j)) = ∑ i, (star T) j i * T i j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.star_apply, Complex.star_def, mul_comm]
      _ = (star T * T) j j := rfl
      _ = 1 := by rw [h, Matrix.one_apply_eq]

private noncomputable def mixedTerms (a b : Fin 3 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] ℂ where
  toFun M := ∑ i, ∑ j,
    M i j • (complementProduct a i * b j + a i * complementProduct b j)
  map_add' M N := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r M := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

private theorem mixedTerms_perm (a b : Fin 3 → ℂ) (σ : Equiv.Perm (Fin 3)) :
    mixedTerms a b (σ.permMatrix ℝ) =
      ∑ i, (complementProduct a i * b (σ i) + a i * complementProduct b (σ i)) := by
  change (∑ i, ∑ j, (σ.permMatrix ℝ) i j •
    (complementProduct a i * b j + a i * complementProduct b j)) = _
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (σ i)]
  · simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  · intro j _ hj
    simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Ne.symm hj]
  · simp

private theorem mixedTerms_vertex (a b : Fin 3 → ℂ) (σ : Equiv.Perm (Fin 3)) :
    (∏ i, (a i + b (σ i))) = (∏ i, a i) + (∏ i, b i) + mixedTerms a b (σ.permMatrix ℝ) := by
  let b' := b ∘ σ
  have hprod : (∏ i, b' i) = ∏ i, b i := Equiv.prod_comp σ b
  calc
    _ = (diagonal a + diagonal b').det := by rw [Matrix.diagonal_add, Matrix.det_diagonal]; rfl
    _ = _ := by
      rw [det_diagonal_add_three, Matrix.det_diagonal, hprod, Matrix.adjugate_diagonal,
        mixedTerms_perm]
      simp only [Matrix.diagonal_apply_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      change complementProduct a i * b (σ i) + a i * complementProduct (b ∘ σ) i = _
      rw [complementProduct_reindex]

private theorem mixedTerms_unitary (a b : Fin 3 → ℂ) (W : Matrix.unitaryGroup (Fin 3) ℂ) :
    (diagonal a + (W : Matrix (Fin 3) (Fin 3) ℂ) * diagonal b *
      star (W : Matrix (Fin 3) (Fin 3) ℂ)).det =
      (∏ i, a i) + (∏ i, b i) +
        mixedTerms a b (Matrix.of fun i j => Complex.normSq ((W : Matrix (Fin 3) (Fin 3) ℂ) i j)) := by
  let T : Matrix (Fin 3) (Fin 3) ℂ := W
  have hdet : (T * diagonal b * star T).det = ∏ i, b i := by
    have hW : T * star T = 1 := Unitary.coe_mul_star_self W
    have h := congrArg Matrix.det hW
    simp only [Matrix.det_mul, Matrix.det_one] at h
    simp only [Matrix.det_mul, Matrix.det_diagonal]
    rw [mul_right_comm T.det (∏ i, b i) (star T).det, h, one_mul]
  rw [det_diagonal_add_three, hdet, adjugate_conj_unitary, Matrix.adjugate_diagonal]
  congr 1
  change (∑ i, (complementProduct a i * (T * diagonal b * star T) i i +
      a i * (T * diagonal (complementProduct b) * star T) i i)) =
    ∑ i, ∑ j, Complex.normSq (T i j) • (complementProduct a i * b j + a i * complementProduct b j)
  apply Finset.sum_congr rfl
  intro i _
  simp only [diag_conj_apply, Finset.mul_sum, ← Finset.sum_add_distrib, Complex.real_smul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem unitary_case_three (a b : Fin 3 → ℂ) (W : Matrix.unitaryGroup (Fin 3) ℂ) :
    (diagonal a + (W : Matrix (Fin 3) (Fin 3) ℂ) * diagonal b *
      star (W : Matrix (Fin 3) (Fin 3) ℂ)).det ∈
    convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin 3) => ∏ i, (a i + b (σ i))) := by
  obtain ⟨w, hw, hsum, hdecomp⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic (unitary_normSq_doublyStochastic W)
  refine mem_convexHull_of_exists_fintype w
    (fun σ => ∏ i, (a i + b (σ i))) hw hsum (fun σ => ⟨σ, rfl⟩) ?_
  have hlin := congrArg (mixedTerms a b) hdecomp
  simp only [map_sum, map_smul] at hlin
  rw [mixedTerms_unitary, ← hlin]
  simp_rw [mixedTerms_vertex a b, smul_add, Finset.sum_add_distrib,
    ← Finset.sum_smul, hsum, one_smul]

end OMA.MarcusThree

/-- The three-dimensional determinant lies in the required convex hull. -/
theorem OMA.solution : OMA.R_mo_42902_R1.H1 := by
  intro α β U V
  dsimp only
  rw [OMA.R_mo_42902_R1.relative_det]
  exact OMA.MarcusThree.unitary_case_three α β (star U * V)
