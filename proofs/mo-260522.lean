import OMAStatements.S_mo_260522

namespace OMA.S_mo_260522
open Matrix
private abbrev RatMat := Matrix (Fin 5) (Fin 5) ℚ
private def Aq : RatMat :=
  !![65536,0,0,0,-1;
      -65536,4096,0,0,0;
      0,-4096,256,0,0;
      0,0,-256,16,0;
      0,0,0,-16,1]

private def Wq : RatMat :=
  (2490258744483 : ℚ)⁻¹ • !![1791530810469,992731667316,706209821844,592904912280,1075184290644;
      -1728703276684,1096294514895,706213713402,593579700740,1077050259802;
      -58205222156,-2001740222598,826169163135,594178042660,1074911073218;
      -1758147720,-83806063260,-2124296045340,720121359717,1078495992660;
      108750644,-4838676198,-93430822782,-2150788971340,1251695918335]

private def Xq : RatMat :=
  (100 : ℚ)⁻¹ • !![-21511,-2897,-498,-92,0;
      21553,-2880,-498,-92,0;
      -42,5788,-493,-92,0;
      0,-13,1491,-91,0;
      0,2,-2,367,0]

private def Yq : RatMat :=
  (27252117605398 : ℚ)⁻¹ • !![-8294567358779850,-60343296298250,-2217536313370,-5252472208270,0;
      259991320921425,-1928054034060175,-18741726135335,2051120940715,0;
      -23914551525,80618100996475,-468245283914765,-5775698038215,0;
      -23795148625,162345304975,24568696464935,-110323466582315,0;
      39420602575,332265943975,3023106127335,15794159867885,0]
private def xq : Fin 5 → ℚ := ![2,3,1,-3,-3]
end OMA.S_mo_260522

namespace OMA.S_mo_260522
open Matrix Finset
set_option maxRecDepth 16000 in
set_option maxHeartbeats 9000000 in
private lemma certificate_q :
    Wqᵀ*Wq=1 ∧ Aq+(1/8:ℚ) • vecMulVec xq xq=Xq*Yqᵀ ∧
    (Xqᵀ*Xq).trace+(Yqᵀ*Yq).trace < 2*(Wqᵀ*Aq).trace := by decide +kernel

private noncomputable def liftQ : RatMat →+* Mat 5 := (Rat.castHom ℝ).mapMatrix
private lemma lift_trans (A : RatMat) : liftQ Aᵀ=(liftQ A)ᵀ := rfl
private lemma lift_trace (A : RatMat) : ((A.trace:ℚ):ℝ)=(liftQ A).trace :=
  AddMonoidHom.map_trace (Rat.castHom ℝ) A
private lemma real_certificate : ∃ W X Y : Mat 5, Wᵀ*W=1 ∧
    cycleExample+(1/8:ℝ) • vecMulVec direction direction=X*Yᵀ ∧
    (Xᵀ*X).trace+(Yᵀ*Y).trace < 2*(Wᵀ*cycleExample).trace := by
  have ha : liftQ Aq=cycleExample := rfl
  have hd : liftQ ((1/8:ℚ) • vecMulVec xq xq)=(1/8:ℝ) • vecMulVec direction direction := by
    ext i j
    change (↑((1/8:ℚ)*(xq i*xq j)):ℝ)=(1/8:ℝ)*(direction i*direction j)
    have hv (k : Fin 5) : (xq k : ℝ)=direction k := by fin_cases k <;> norm_num [xq,direction]
    push_cast
    rw [hv,hv]
  refine ⟨liftQ Wq,liftQ Xq,liftQ Yq,?_,?_,?_⟩
  · have h := congrArg liftQ certificate_q.1
    simpa only [map_mul,lift_trans,map_one] using h
  · have h := congrArg liftQ certificate_q.2.1
    simpa only [map_add,map_mul,lift_trans,ha,hd] using h
  · have h : (((Xqᵀ*Xq).trace:ℚ):ℝ)+(((Yqᵀ*Yq).trace:ℚ):ℝ) <
        2*(((Wqᵀ*Aq).trace:ℚ):ℝ) := by exact_mod_cast certificate_q.2.2
    simpa only [lift_trace,map_mul,lift_trans,ha] using h
end OMA.S_mo_260522

namespace OMA.S_mo_260522
open Matrix Finset
private lemma factored_bound {n : ℕ} (Q X Y : Mat n) (hq : Qᵀ*Q=1) :
    2*(Qᵀ*(X*Yᵀ)).trace ≤ (Xᵀ*X).trace+(Yᵀ*Y).trace := by
  have hp := (Matrix.posSemidef_conjTranspose_mul_self (X-Q*Y)).trace_nonneg
  change 0 ≤ ((X-Q*Y)ᵀ*(X-Q*Y)).trace at hp
  have h2 : (Yᵀ*Qᵀ*X).trace = (Qᵀ*(X*Yᵀ)).trace := calc
    _ = (Yᵀ*(Qᵀ*X)).trace := by rw [Matrix.mul_assoc]
    _ = ((Qᵀ*X)*Yᵀ).trace := trace_mul_comm _ _
    _ = _ := by rw [Matrix.mul_assoc]
  have h1 : (Xᵀ*(Q*Y)).trace = (Qᵀ*(X*Yᵀ)).trace := by
    rw [← Matrix.trace_transpose (Xᵀ*(Q*Y)),transpose_mul,transpose_mul,transpose_transpose]
    exact h2
  have h3 : Yᵀ*Qᵀ*(Q*Y)=Yᵀ*Y := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc Qᵀ Q Y,hq,Matrix.one_mul]
  rw [transpose_sub,transpose_mul,sub_mul,mul_sub,mul_sub,h3,
    trace_sub,trace_sub,trace_sub,h1,h2] at hp
  linarith

private lemma perturbed_trace {n : ℕ} (Q A : Mat n) (t : ℝ) (x : Fin n → ℝ) :
    (Qᵀ*(A+t • vecMulVec x x)).trace =
    (Qᵀ*A).trace+t*(x ⬝ᵥ (Q*ᵥx)) := by
  rw [Matrix.mul_add,Matrix.mul_smul,trace_add,trace_smul,mul_vecMulVec,trace_vecMulVec]
  rw [dotProduct_comm (Qᵀ*ᵥx) x,dotProduct_transpose_mulVec]
  rfl
end OMA.S_mo_260522

namespace OMA.S_mo_260522
open Matrix Finset
private lemma cycle_shape :
    (∀ j, 0 < cycleExample j j) ∧
    (∀ i j, i≠j → cycleExample i j ≤ 0) ∧
    (∀ j, (∑ i,cycleExample i j)=0 ∧
      (∑ i ∈ univ.erase j, |cycleExample i j|)=cycleExample j j) ∧
    cycleExample.det=0 ∧ cycleExampleᵀ≠cycleExample := by
  have diag (j : Fin 5) : 0 < cycleExample j j := by fin_cases j <;> norm_num [cycleExample,cycleQ]
  have off (i j : Fin 5) (h : i≠j) : cycleExample i j≤0 := by
    fin_cases i <;> fin_cases j <;> first | exact (h rfl).elim | norm_num [cycleExample,cycleQ]
  have col (j : Fin 5) : (∑ i,cycleExample i j)=0 := by
    fin_cases j <;> norm_num [cycleExample,cycleQ,Fin.sum_univ_succ]
  refine ⟨diag,off,fun j => ⟨col j,?_⟩,?_,?_⟩
  · have hneg := sum_congr (s₁:=univ.erase j) (s₂:=univ.erase j) rfl
      (fun i hi => abs_of_nonpos (off i j (mem_erase.mp hi).1))
    rw [hneg,sum_neg_distrib]
    have h := sum_erase_add (f:=fun i => cycleExample i j) univ (mem_univ j)
    linarith [col j]
  · have hv : cycleExampleᵀ *ᵥ (1 : Fin 5 → ℝ)=0 := by
      ext j
      simpa [mulVec,dotProduct] using col j
    have h := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hv
      (i:=0) (by simp)
    simpa using h
  · intro hs
    have h := congrArg (fun M : Mat 5 => M 0 1) hs
    norm_num [cycleExample,cycleQ,transpose_apply] at h
end OMA.S_mo_260522

namespace OMA.S_mo_260522
open Matrix ComplexStarModule
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule

lemma negative_spectrum {n : ℕ} (Q : Mat n) (hQ : Qᵀ * Q = 1) (x : Fin n → ℝ)
    (hx : x ⬝ᵥ (Q *ᵥ x) < 0) : ∃ z ∈ spectrum ℂ (complexify Q), z.re < 0 := by
  classical
  let U := complexify Q
  have hstar : star U = Uᵀ := by
    ext i j
    simp [U, complexify]
  have hmap : Uᵀ * U = 1 := by
    change ((Qᵀ).map (algebraMap ℝ ℂ)) * (Q.map (algebraMap ℝ ℂ)) = 1
    simp only [← RingHom.mapMatrix_apply, ← map_mul, hQ, map_one]
  have hnorm : IsStarNormal U := isStarNormal_of_mem_unitary
    (Matrix.mem_unitaryGroup_iff'.mpr (hstar ▸ hmap))
  by_contra! h
  have hp : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ (ℜ U : Matrix (Fin n) (Fin n) ℂ) := by
    apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ℜ U).2).2
    rw [spectrum_realPart' U hnorm]
    rintro _ ⟨z,hz,rfl⟩
    exact h z hz
  let y : Fin n → ℂ := (algebraMap ℝ ℂ) ∘ x
  have hstar_y : star y = y := by ext i; simp [y]
  have hquad := hp.posSemidef.dotProduct_mulVec_nonneg y
  rw [realPart_apply_coe, hstar, hstar_y, Matrix.smul_mulVec, dotProduct_smul,
    Matrix.add_mulVec, dotProduct_add, Matrix.dotProduct_transpose_mulVec] at hquad
  have hq : (y ⬝ᵥ (U *ᵥ y)) = ((x ⬝ᵥ (Q *ᵥ x) : ℝ) : ℂ) := by
    have hm : U *ᵥ y = (algebraMap ℝ ℂ) ∘ (Q *ᵥ x) :=
      funext fun i => ((algebraMap ℝ ℂ).map_mulVec Q x i).symm
    rw [hm]
    exact ((algebraMap ℝ ℂ).map_dotProduct x (Q *ᵥ x)).symm
  rw [hq] at hquad
  have hreal := hquad.1
  simp [Complex.real_smul] at hreal
  linarith

end OMA.S_mo_260522

namespace OMA.S_mo_260522
open Matrix Finset

lemma polar_max {n : ℕ} (A Q W H : Mat n) (hq : Qᵀ*Q=1) (hw : Wᵀ*W=1)
    (h : H.PosSemidef) (ha : A=Q*H) : (Wᵀ*A).trace ≤ (Qᵀ*A).trace := by
  have hs : Hᵀ=H := (Matrix.isHermitian_iff_isSymm.mp h.1).eq
  have hc : (Qᵀ*W*H).trace=(Wᵀ*Q*H).trace := by
    rw [←Matrix.trace_transpose (Qᵀ*W*H),transpose_mul,transpose_mul,transpose_transpose,hs,
      trace_mul_comm]
  have hp := (h.mul_mul_conjTranspose_same (W-Q)).trace_nonneg
  change 0 ≤ ((W-Q)*H*(W-Q)ᵀ).trace at hp
  rw [trace_mul_cycle,transpose_sub,sub_mul,mul_sub,mul_sub,hw,hq,sub_mul,sub_mul,sub_mul,
    one_mul,trace_sub,trace_sub,trace_sub,hc] at hp
  rw [ha,←Matrix.mul_assoc,←Matrix.mul_assoc,hq,one_mul]
  linarith

end OMA.S_mo_260522

namespace OMA.S_mo_260522
open Matrix Finset
private lemma polar_negative (Q H : Mat 5) (hq : Qᵀ*Q=1) (hH : H.PosSemidef)
    (ha : cycleExample=Q*H) : direction ⬝ᵥ (Q*ᵥdirection) < 0 ∧
    ∃ z∈spectrum ℂ (complexify Q), z.re < 0 := by
  obtain ⟨W,X,Y,hw,hm,hc⟩ := real_certificate
  have hopt := polar_max cycleExample Q W H hq hw hH ha
  have htest := factored_bound Q X Y hq
  rw [← hm,perturbed_trace] at htest
  have hneg : direction ⬝ᵥ (Q*ᵥdirection)<0 := by linarith
  exact ⟨hneg,negative_spectrum Q hq _ hneg⟩
end OMA.S_mo_260522

open OMA.S_mo_260522 Matrix
theorem OMA.solution : type_of% @OMA.S_mo_260522.main := by
  obtain ⟨hd,ho,hc,hr,hs⟩ := cycle_shape
  refine ⟨hd,ho,hc,hr,hs,polar_negative,?_⟩
  intro W V d hw hv hD hA
  have hv' : V*Vᵀ=1 := mul_eq_one_comm.mp hv
  have hq : (W*Vᵀ)ᵀ*(W*Vᵀ)=1 := by
    rw [transpose_mul,transpose_transpose,Matrix.mul_assoc,← Matrix.mul_assoc Wᵀ W Vᵀ,hw,
      Matrix.one_mul,hv']
  have hp := (Matrix.PosSemidef.diagonal hD).mul_mul_conjTranspose_same V
  apply (polar_negative (W*Vᵀ) (V*diagonal d*Vᵀ) hq hp ?_).2
  rw [hA]
  simp only [Matrix.mul_assoc,← Matrix.mul_assoc Vᵀ V,hv,Matrix.one_mul]
