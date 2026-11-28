import OMAStatements.S_mo_421810

/-!
# Common critical points of graph characteristic polynomials

Source: baronbrixius, https://mathoverflow.net/questions/421810 (CC BY-SA 4.0).
Credit: @connoranderson.

For a real symmetric matrix let P = XI−A, Q = adj(P), f = det(P).
Differentiating PQ=fI and multiplying by Q gives Q²+fQ'=f'Q.
Its i-th diagonal entry is a sum of squares at every real point
and Qᵢᵢ is the characteristic polynomial of the principal deletion.
If the two derivatives vanish, the i-th row of the evaluated adjugate
vanishes. Cofactor expansion gives f=0 there. Rolle's theorem and
the spectral theorem ensure every complex root of f' is real.
-/

namespace OMA.S_mo_421810

open Polynomial

/-- Rolle's inequality counts enough real derivative roots with multiplicity to
exhaust the degree of the derivative of a real-split polynomial. -/
private lemma derivative_splits_real (p : Polynomial ℝ) (h : p.Splits) : p.derivative.Splits := by
  apply splits_iff_card_roots.mpr
  apply (card_roots' _).antisymm
  have hc := card_roots_le_derivative p
  rw [← h.natDegree_eq_card_roots] at hc
  rw [natDegree_derivative]
  omega

lemma common_root_real {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : A.IsHermitian) (z : ℂ) (hz : Polynomial.aeval z A.charpoly.derivative = 0) :
    ∃ t : ℝ, z = (t : ℂ) := by
  have hd : A.charpoly.derivative ≠ 0 := derivative_ne_zero.mpr (by simp)
  have hs := derivative_splits_real _ hA.splits_charpoly
  have hr : (A.charpoly.derivative.map (algebraMap ℝ ℂ)).IsRoot z := by
    simpa [IsRoot, eval_map, aeval_def] using hz
  obtain ⟨t, ht⟩ := hs.mem_range_of_isRoot hd hr
  exact ⟨t, ht.symm⟩

end OMA.S_mo_421810

namespace OMA.S_mo_421810
open Polynomial Matrix
open scoped Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def D (A : Matrix ι ι ℝ[X]) : Matrix ι ι ℝ[X] :=
  A.map Polynomial.derivative

omit [DecidableEq ι] in
private lemma D_mul (A B : Matrix ι ι ℝ[X]) :
    D (A*B) = D A * B + A * D B := by
  ext i j
  simp [D,Matrix.mul_apply,derivative_mul,Finset.sum_add_distrib]

private lemma D_charmatrix (A : Matrix ι ι ℝ) : D A.charmatrix = 1 := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [D]
  · simp [D,h]

omit [Fintype ι] in
private lemma D_scalar (f : ℝ[X]) : D (f • (1 : Matrix ι ι ℝ[X])) =
    f.derivative • (1 : Matrix ι ι ℝ[X]) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [D]
  · simp [D,h]

lemma adjugate_identity (A : Matrix ι ι ℝ) :
    A.charmatrix.adjugate * A.charmatrix.adjugate + A.charpoly • D A.charmatrix.adjugate =
      A.charpoly.derivative • A.charmatrix.adjugate := by
  let P := A.charmatrix
  let Q := P.adjugate
  have pc : P*Q = A.charpoly • (1 : Matrix ι ι ℝ[X]) := P.mul_adjugate
  have cp : Q*P = A.charpoly • (1 : Matrix ι ι ℝ[X]) := P.adjugate_mul
  have hh := congrArg D pc
  rw [D_mul,D_scalar,show D P = 1 from D_charmatrix A,Matrix.one_mul] at hh
  have e := congrArg (fun M => Q*M) hh
  simpa only [Matrix.mul_add,← Matrix.mul_assoc,cp,Matrix.smul_mul,Matrix.one_mul,
    Matrix.mul_smul,Matrix.mul_one,Q,P] using e

lemma cofactor_delete {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (i : Fin (n+1)) :
    A.charmatrix.adjugate i i = (A.submatrix i.succAbove i.succAbove).charpoly := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix,← two_mul]
  have hs : (-1 : ℝ[X])^(2*(i:ℕ))=1 := by rw [pow_mul];norm_num
  rw [hs,one_mul,Matrix.charpoly]
  apply congrArg Matrix.det
  ext j k
  by_cases h : j=k
  · subst k
    simp
  · have h' : i.succAbove j ≠ i.succAbove k := fun e => h (i.succAbove_right_injective e)
    simp [h,h',Matrix.submatrix_apply]

lemma real_common_root {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.IsSymm)
    (i : Fin (n+1)) (t : ℝ) (hf : A.charpoly.derivative.eval t=0)
    (hg : (A.submatrix i.succAbove i.succAbove).charpoly.derivative.eval t=0) :
    A.charpoly.eval t=0 := by
  let P := A.charmatrix
  let Q := P.adjugate
  have hc : P.IsSymm := by
    change A.charmatrix.transpose = A.charmatrix
    rw [← Matrix.charmatrix_transpose,hA.eq]
  have sym (j : Fin (n+1)) : Q j i = Q i j := hc.adjugate.apply i j
  have d : (D Q i i).eval t=0 := by
    change (A.charmatrix.adjugate i i).derivative.eval t=0
    rwa [cofactor_delete]
  have identity := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ[X] => (M i i).eval t)
    (adjugate_identity A)
  change (((Q*Q) i i + A.charpoly * D Q i i).eval t) =
    (A.charpoly.derivative * Q i i).eval t at identity
  have ss : (∑ j : Fin (n+1), (Q i j).eval t ^ 2) = 0 := by
    simpa only [Matrix.mul_apply,eval_add,eval_finsetSum,eval_mul,hf,d,mul_zero,zero_mul,
      add_zero,sym,← sq,eval_pow] using identity
  have hz (j : Fin (n+1)) : (Q j i).eval t=0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ((Q i j).eval t))).mp ss j
      (Finset.mem_univ j)
    rw [sym j]
    exact (sq_eq_zero_iff).mp h
  change P.det.eval t=0
  rw [Matrix.det_eq_sum_mul_adjugate_row P i,eval_finsetSum]
  apply Finset.sum_eq_zero
  intro j _
  exact (eval_mul ..).trans (by rw [show (P.adjugate j i).eval t=0 from hz j,mul_zero])

end OMA.S_mo_421810

open OMA.S_mo_421810
theorem OMA.solution : type_of% @OMA.S_mo_421810.main := by
  classical
  intro n G i z hf hg
  let A := adj G
  have hs : A.IsHermitian := G.isHermitian_adjMatrix ℝ
  obtain ⟨t,rfl⟩ := common_root_real A hs z hf
  have ev (p : Polynomial ℝ) : Polynomial.aeval (t:ℂ) p = Complex.ofReal (p.eval t) := by
    exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A:=ℂ) t p
  apply (ev _).trans
  apply Complex.ofReal_eq_zero.mpr
  apply real_common_root A (Matrix.isHermitian_iff_isSymm.mp hs) i t
  · exact Complex.ofReal_eq_zero.mp ((ev _).symm.trans hf)
  · exact Complex.ofReal_eq_zero.mp ((ev _).symm.trans hg)
