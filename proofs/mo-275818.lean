import OMAStatements.S_mo_275818

namespace OMA.S_mo_275818
open Matrix Finset

private lemma adm2 {A : Mat} (hn : A 0 1 ≠ A 1 0)
    (h00 : 0<A 0 0) (h11 : 0<A 1 1) (h01 : A 0 1<0) (h10 : A 1 0<0)
    (h0 : -A 0 1 ≤ A 0 0) (h1 : -A 1 0 ≤ A 1 1) : admissible A := by
  refine ⟨fun h => hn (h.apply 1 0),?_,?_,?_⟩
  · intro i; fin_cases i <;> assumption
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    have e0 : (univ.erase (0:Fin 2))={1} := by decide
    have e1 : (univ.erase (1:Fin 2))={0} := by decide
    fin_cases i <;> simp_all [abs_of_neg]

private lemma witness_facts : admissible witness ∧ witness.rank=1 ∧
    ∃ U V U' : Mat, ∃ s : Fin 2 → ℝ, svd witness U V s ∧ svd witness U' V s ∧
      (U*Vᵀ).trace=0 ∧ (U'*Vᵀ).trace=8/5 := by
  refine ⟨by apply adm2 <;> norm_num [witness],?_,?_⟩
  · have hrep : witness = vecMulVec ![(7:ℝ),-1] ![1,-1] := by
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [witness,vecMulVec]
    have hup := rank_vecMulVec_le ![(7:ℝ),-1] ![1,-1]
    rw [← hrep] at hup
    let e (_ : Fin 1) : Fin 2 := 0
    have hsmall : (witness.submatrix e e).det ≠ 0 := by norm_num [Matrix.det_fin_one,e,witness]
    have hh := Matrix.rank_of_det_ne_zero hsmall
    have hl := Matrix.rank_submatrix_le witness e e
    rw [hh] at hl
    simpa using Nat.le_antisymm hup (by simpa using hl)
  · let c := Real.sqrt 2/2
    have hc : c*c=1/2 := by dsimp [c]; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    let V : Mat := !![c,c;-c,c]
    let U : Mat := !![7*c/5,-c/5;-c/5,-7*c/5]
    let U' : Mat := !![7*c/5,c/5;-c/5,7*c/5]
    let s : Fin 2 → ℝ := ![10,0]
    have hv : orth V := by
      constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [V,Matrix.mul_apply,Fin.sum_univ_two,transpose_apply,Matrix.one_apply] <;> nlinarith
    have hu : orth U := by
      constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [U,Matrix.mul_apply,Fin.sum_univ_two,transpose_apply,Matrix.one_apply] <;> nlinarith
    have hu' : orth U' := by
      constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [U',Matrix.mul_apply,Fin.sum_univ_two,transpose_apply,Matrix.one_apply] <;> nlinarith
    refine ⟨U,V,U',s,⟨hu,hv,by norm_num [s],by norm_num [s],?_⟩,
      ⟨hu',hv,by norm_num [s],by norm_num [s],?_⟩,?_,?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [witness,U,V,s,Matrix.mul_apply,Fin.sum_univ_two,transpose_apply,diagonal,Matrix.vecHead,Matrix.vecTail] <;> nlinarith
    · ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [witness,U',V,s,Matrix.mul_apply,Fin.sum_univ_two,transpose_apply,diagonal,Matrix.vecHead,Matrix.vecTail] <;> nlinarith
    · norm_num [U,V,Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,transpose_apply]; nlinarith
    · norm_num [U',V,Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,transpose_apply]; nlinarith

end OMA.S_mo_275818

namespace OMA.S_mo_275818
open Matrix Finset
private theorem lower (A U V : Mat) (s : Fin 2 → ℝ) (ha : admissible A) (hn : A.det≠0)
    (hs : svd A U V s) : (U*Vᵀ).trace=2*A.trace/Real.sqrt (A.trace^2+(A 1 0-A 0 1)^2) ∧
    Real.sqrt 2 < (U*Vᵀ).trace := by
  obtain ⟨_,hd,ho,hw⟩ := ha
  obtain ⟨hu,hv,hs1,hs0,hA⟩ := hs
  have h01 := ho 0 1 (by decide)
  have h10 := ho 1 0 (by decide)
  have h0 := hw 0
  have h1 := hw 1
  have cut0 : (univ.erase (0:Fin 2)) = {1} := by decide
  have cut1 : (univ.erase (1:Fin 2)) = {0} := by decide
  simp [cut0,abs_of_neg h01] at h0
  simp [cut1,abs_of_neg h10] at h1
  have hdet : 0 < A.det := by
    apply lt_of_le_of_ne _ hn.symm
    rw [Matrix.det_fin_two]
    nlinarith [mul_nonneg (by linarith : 0 ≤ A 0 0+A 0 1) (hd 1).le,
      mul_nonneg (by linarith : 0 ≤ A 1 1+A 1 0) (neg_nonneg.mpr h01.le)]
  let Q := U*Vᵀ
  let H := V*diagonal s*Vᵀ
  have horth : Qᵀ*Q=1 := by
    dsimp [Q]; rw [transpose_mul,transpose_transpose,Matrix.mul_assoc,← Matrix.mul_assoc Uᵀ,
      hu.1,one_mul,hv.2]
  have hdSq := congrArg det horth
  rw [det_mul,det_transpose,det_one] at hdSq
  have hAd : A.det=Q.det*(s 0*s 1) := by
    rw [hA]; simp [Q,Matrix.det_mul,Fin.prod_univ_two]; ring
  have hsgn : Q.det=1 := by
    have hprod := mul_nonneg (hs1.trans hs0) hs1
    rcases (mul_self_eq_one_iff).1 hdSq with pos|neg
    · exact pos
    · rw [neg] at hAd; linarith
  have qadj : Qᵀ=Q.adjugate := by
    calc Qᵀ = Qᵀ*(Q*Q.adjugate) := by rw [mul_adjugate,hsgn,one_smul,mul_one]
         _ = Q.adjugate := by rw [← Matrix.mul_assoc,horth,one_mul]
  have qdiag := congrFun (congrFun qadj 0) 0
  have qoff := congrFun (congrFun qadj 1) 0
  simp [adjugate_fin_two,transpose_apply] at qdiag qoff
  have h11 : Q 1 1=Q 0 0 := by linarith
  have h01' : Q 0 1= -Q 1 0 := by linarith
  have hnorm := congrFun (congrFun horth 0) 0
  simp [Matrix.mul_apply,Fin.sum_univ_two,transpose_apply] at hnorm
  have hqh : Q*H=A := by
    rw [hA]; dsimp [Q,H]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᵀ V, hv.1,one_mul]
  have hsymm : Hᵀ=H := by simp [H,transpose_mul,Matrix.mul_assoc]
  have hcross := congrFun (congrFun hsymm 0) 1
  change H 1 0 = H 0 1 at hcross
  have htr : 0 < A.trace := by simp [Matrix.trace,Fin.sum_univ_two]; linarith [hd 0,hd 1]
  have hH : H.trace=s 0+s 1 := by
    rw [show H=V*diagonal s*Vᵀ from rfl,trace_mul_cycle,hv.1,one_mul]
    simp [Matrix.trace,Fin.sum_univ_two]
  have tt : A.trace=Q 0 0*H.trace := by
    rw [← hqh]; simp [Matrix.trace,Fin.sum_univ_two,Matrix.mul_apply,h11,h01',hcross]; ring
  have dd : A 1 0-A 0 1=Q 1 0*H.trace := by
    rw [← hqh]; simp [Matrix.trace,Fin.sum_univ_two,Matrix.mul_apply,h11,h01',hcross]; ring
  have hpos : 0 < H.trace := by
    have hh : 0 ≤ H.trace := by rw [hH]; linarith
    apply lt_of_le_of_ne hh
    intro hz; rw [← hz,mul_zero] at tt; linarith
  have root : Real.sqrt (A.trace^2+(A 1 0-A 0 1)^2) = H.trace := by
    rw [tt,dd,show (Q 0 0*H.trace)^2+(Q 1 0*H.trace)^2=H.trace^2 by
      linear_combination H.trace^2*hnorm,Real.sqrt_sq hpos.le]
  have qt : Q.trace=2*Q 0 0 := by simp [Matrix.trace,Fin.sum_univ_two,h11]; ring
  change Q.trace = _ ∧ _ < Q.trace
  rw [root,qt]
  constructor
  · apply (eq_div_iff hpos.ne').2
    rw [tt]; ring
  · have trA : A.trace = A 0 0+A 1 1 := by simp [Matrix.trace,Fin.sum_univ_two]
    have hl : -(A.trace) < A 1 0-A 0 1 := by rw [trA]; linarith [hd 0]
    have hr : A 1 0-A 0 1 < A.trace := by rw [trA]; linarith [hd 1]
    rw [tt,dd,← neg_mul] at hl
    rw [tt,dd] at hr
    have hl' := (mul_lt_mul_iff_left₀ hpos).1 hl
    have hr' := (mul_lt_mul_iff_left₀ hpos).1 hr
    nlinarith [mul_pos (by linarith : 0<Q 0 0+Q 1 0) (by linarith : 0<Q 0 0-Q 1 0),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg 2]
end OMA.S_mo_275818

namespace OMA.S_mo_275818
open Matrix Finset
set_option maxHeartbeats 1200000 in
private theorem approach (ε : ℝ) (hε : 0 < ε) : ∃ (A U V : Mat) (s : Fin 2 → ℝ),
    admissible A ∧ strict A ∧ A.det ≠ 0 ∧ svd A U V s ∧ (U*Vᵀ).trace < Real.sqrt 2+ε := by
  let v := min (ε/4) (1/4)
  let u := Real.sqrt (1-v^2)
  let c := Real.sqrt 2/2
  have hv : 0 < v := lt_min (by positivity) (by norm_num)
  have hv' : v ≤ 1/4 := min_le_right _ _
  have hvε : v ≤ ε/4 := min_le_left _ _
  have hu2 : u^2=1-v^2 := Real.sq_sqrt (by nlinarith [mul_nonneg hv.le (by linarith : 0 ≤ 1/4-v)])
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hule : u ≤ 1 := by nlinarith [sq_nonneg v]
  have huv : v < u := by
    by_contra! h
    have hh := mul_self_le_mul_self hu0 h
    nlinarith [mul_nonneg hv.le (sub_nonneg.mpr hv')]
  have hu : 0 < u := hv.trans huv
  have hc : 0<c := by dsimp [c]; positivity
  have hc2 : c*c=1/2 := by dsimp [c]; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  let t := v/2
  have ht : 0<t := by dsimp [t]; linarith
  have hts : t ≤ 1 := by dsimp [t]; linarith
  have hy : 0<t*v := mul_pos ht hv
  have hz : 0<t*u := mul_pos ht hu
  have htv : t*v < u := (mul_le_of_le_one_left hv.le hts).trans_lt huv
  have htu : t*u < v := by
    calc t*u ≤ t := mul_le_of_le_one_right ht.le hule
         _ < v := by dsimp [t]; linarith
  let V : Mat := !![c,c;-c,c]
  let U : Mat := !![u,v;-v,u]
  let s : Fin 2 → ℝ := ![1,t]
  let A : Mat := !![c*(u+t*v),c*(-u+t*v);c*(-v+t*u),c*(v+t*u)]
  have hvO : orth V := by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [V,Matrix.mul_apply,Fin.sum_univ_two,transpose_apply,Matrix.one_apply] <;> nlinarith
  have huO : orth U := by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [U,Matrix.mul_apply,Fin.sum_univ_two,transpose_apply,Matrix.one_apply] <;> nlinarith
  have hA : A = U*diagonal s*Vᵀ := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [A,U,V,s,Matrix.mul_apply,Fin.sum_univ_two,diagonal,transpose_apply,Matrix.vecHead,Matrix.vecTail] <;> ring
  have lt1 : A 0 1<0 := mul_neg_of_pos_of_neg hc (by linarith)
  have lt2 : A 1 0<0 := mul_neg_of_pos_of_neg hc (by linarith)
  have g1 : -A 0 1 < A 0 0 := by
    change -(c*(-u+t*v)) < c*(u+t*v)
    rw [← mul_neg]
    apply mul_lt_mul_of_pos_left _ hc
    linarith
  have g2 : -A 1 0 < A 1 1 := by
    change -(c*(-v+t*u)) < c*(v+t*u)
    rw [← mul_neg]
    apply mul_lt_mul_of_pos_left _ hc
    linarith
  refine ⟨A,U,V,s,adm2 ?_ (by linarith) (by linarith) lt1 lt2 g1.le g2.le,?_,?_,
    ⟨huO,hvO,ht.le,hts,hA⟩,?_⟩
  · apply ne_of_lt
    apply mul_lt_mul_of_pos_left _ hc
    nlinarith [mul_pos ht (sub_pos.mpr huv)]
  · intro i
    have e0 : (univ.erase (0:Fin 2))={1} := by decide
    have e1 : (univ.erase (1:Fin 2))={0} := by decide
    fin_cases i <;> simp_all [abs_of_neg]
  · have hdu : U.det=1 := by simp [U,Matrix.det_fin_two]; nlinarith
    have hdv : V.det=1 := by simp [V,Matrix.det_fin_two]; nlinarith
    rw [hA,Matrix.det_mul,Matrix.det_mul,det_transpose,Matrix.det_diagonal,Fin.prod_univ_two]
    simp [hdu,hdv,s,ht.ne']
  · have tr : (U*Vᵀ).trace=2*c*(u+v) := by
      simp [U,V,Matrix.trace,Matrix.vecMul,dotProduct,Fin.sum_univ_two,transpose_apply]; ring
    rw [tr]
    have hc' : c ≤ 1 := by nlinarith
    have hcEq : Real.sqrt 2=2*c := by dsimp [c]; ring
    have hcu := mul_le_of_le_one_right hc.le hule
    have hcv := mul_le_of_le_one_left hv.le hc'
    rw [hcEq]
    linarith
end OMA.S_mo_275818

open OMA.S_mo_275818
theorem OMA.solution : type_of% @OMA.S_mo_275818.main := by
  exact ⟨witness_facts,lower,approach⟩
