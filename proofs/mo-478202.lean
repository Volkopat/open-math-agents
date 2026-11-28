import OMAStatements.S_mo_478202

/-! Credit: @connoranderson; follows the trace-power argument of WhatsUp and Dave Benson. -/

namespace OMA.S_mo_478202

open Matrix Polynomial
open scoped Polynomial

private lemma roots_card {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    A.charpoly.roots.card=d := by
  rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots]
  simp

private lemma linear_det {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (c : ℂ) :
    (A - algebraMap ℂ _ c).det = (A.charpoly.roots.map (fun z => z-c)).prod := by
  have h := (IsAlgClosed.splits A.charpoly).eval_eq_prod_roots_of_monic A.charpoly_monic c
  rw [eval_charpoly] at h
  calc
    _ = (-1 : ℂ)^d * (Matrix.scalar (Fin d) c - A).det := by
      simpa [Matrix.algebraMap_eq_diagonal,Pi.algebraMap_def] using det_neg (Matrix.scalar (Fin d) c-A)
    _ = _ := by
      rw [h]
      conv_rhs => rw [show (fun z : ℂ => z-c)=(fun z => (-1)*(c-z)) from funext fun z => by ring]
      rw [Multiset.prod_map_mul,Multiset.map_const',Multiset.prod_replicate,roots_card]

private lemma det_polynomial {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (p : ℂ[X]) :
    (aeval A p).det = (A.charpoly.roots.map (fun z => p.eval z)).prod := by
  let good (q : ℂ[X]) := (aeval A q).det = (A.charpoly.roots.map fun z => q.eval z).prod
  have hmul (f g : ℂ[X]) (hf : good f) (hg : good g) : good (f*g) := by
    simpa only [good,map_mul,det_mul,eval_mul,Multiset.prod_map_mul] using congrArg₂ (·*·) hf hg
  have hlin (c : ℂ) : good (X-C c) := by simpa [good] using linear_det A c
  have hfac (m : Multiset ℂ) : good ((m.map fun c => X-C c).prod) := by
    induction m using Multiset.induction_on with
    | empty => simp [good]
    | cons c m ih => simpa using hmul _ _ (hlin c) ih
  have hc (c : ℂ) : good (C c) := by
    simp [good,Matrix.algebraMap_eq_diagonal,Pi.algebraMap_def,roots_card]
  change good p
  exact (congrArg good (IsAlgClosed.splits p).eq_prod_roots).mpr
    (hmul _ _ (hc p.leadingCoeff) (hfac p.roots))

private lemma charpoly_pow_roots {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    (A^k).charpoly.roots = A.charpoly.roots.map (fun z => z^k) := by
  let s := A.charpoly.roots.map (fun z => z^k)
  have h : (A^k).charpoly = (s.map (fun z => X-C z)).prod := by
    apply Polynomial.funext
    intro t
    have e := det_polynomial A (C t-X^k)
    simpa [s,Matrix.algebraMap_eq_diagonal,Pi.algebraMap_def,eval_charpoly,eval_multiset_prod,Multiset.map_map,Function.comp_def] using e
  rw [h,roots_multiset_prod_X_sub_C]

private lemma trace_pow_roots {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    (A^k).trace = (A.charpoly.roots.map fun z => z^k).sum := by
  rw [Matrix.trace_eq_sum_roots_charpoly,charpoly_pow_roots]

end OMA.S_mo_478202
namespace OMA.S_mo_478202

open MvPolynomial

private lemma newton_eq_eval {ι : Type*} [Fintype ι] (z : ι → ℂ) (k : ℕ) :
    newton (fun j => ∑ i, z i^j) k = eval z (esymm ι ℂ k) := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k=0
    · subst k; simp [newton]
    · have hn : (k:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      have h := congrArg (eval z) (mul_esymm_eq_sum ι ℂ k)
      simp only [map_mul,map_natCast,map_pow,map_neg,map_one,map_sum] at h
      simp only [psum,map_sum,map_pow,eval_X] at h
      rw [Finset.sum_filter] at h
      rw [newton,if_neg hk]
      simp_rw [dite_eq_ite]
      simp +contextual only [ih]
      field_simp
      linear_combination -h

private lemma newton_top {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    newton (fun j => ∑ i, z i^j) (Fintype.card ι) = ∏ i, z i := by
  classical
  simp [newton_eq_eval, esymm, ← Finset.card_univ]

end OMA.S_mo_478202
namespace OMA.S_mo_478202

private lemma det_newton {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    A.det = newton (fun j => (A^j).trace) d := by
  let l := A.charpoly.roots.toList
  let z (i : Fin l.length) := l[i.val]
  have hlen : l.length = d := by simp [l,roots_card]
  have hs : (fun j => (A^j).trace) = (fun j => ∑ i, z i^j) := by
    funext j
    rw [trace_pow_roots]
    exact (Fin.sum_univ_fun_getElem l (fun u => u^j)).trans (Multiset.sum_map_toList _ _) |>.symm
  have hp : ∏ i, z i = A.det := by
    rw [Matrix.det_eq_prod_roots_charpoly]
    exact (Fin.prod_univ_getElem l).trans (Multiset.prod_toList _)
  have hnew := newton_top z
  rw [hp,← hs,Fintype.card_fin,hlen] at hnew
  exact hnew.symm

end OMA.S_mo_478202

open OMA.S_mo_478202 in
theorem OMA.solution : type_of% @OMA.S_mo_478202.main := by
  intro G _ _ d ρ γ
  let L := MonoidAlgebra.lift ℂ (Matrix (Fin d) (Fin d) ℂ) G ρ
  rw [det_newton]
  congr 1
  funext k
  change (L γ ^ k).trace = _
  rw [← map_pow,MonoidAlgebra.lift_apply]
  simp [Finsupp.sum,characterPowers,Matrix.trace_sum,Matrix.trace_smul]
