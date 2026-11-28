import OMAStatements.S_mo_345027
namespace OMA.S_mo_345027
open Matrix Finset
open scoped Matrix
private lemma col_cond {n m : ℕ} {A : Fin m → Mat n} {u : Vec n} (h : admissible A u) (j : Fin m) :
    0 < weight A u j ∧ A j *ᵥ u = weight A u j • ((cols A u)ᵀ j) ∧
      ((cols A u)ᵀ j) ⬝ᵥ u = weight A u j := by
  have h0 := Real.sqrt_pos.mpr (h.2.2 j)
  change 0 < weight A u j at h0
  refine ⟨h0,?_,?_⟩
  · funext i;change _ = weight A u j*((A j *ᵥ u) i/weight A u j);field_simp
  · change (∑ i,((A j *ᵥ u) i/weight A u j)*u i)=_
    simp_rw [div_mul_eq_mul_div,←sum_div]
    rw [div_eq_iff h0.ne',←sq,weight,Real.sq_sqrt (h.2.2 j).le,dotProduct]
    exact sum_congr rfl fun i _ => mul_comm _ _

private lemma col_minorant {n : ℕ} (A : Mat n) (h : A.PosSemidef) (u v : Vec n) (w : ℝ)
    (hw : 0<w) (hv : A*ᵥu=w•v) (hu : v ⬝ᵥ u=w) : (A-vecMulVec v v).PosSemidef := by
  have ho : (vecMulVec v v).PosSemidef := by simpa using posSemidef_vecMulVec_self_star v
  apply PosSemidef.of_dotProduct_mulVec_nonneg (h.isHermitian.sub ho.isHermitian)
  intro y
  simp only [star_trivial,sub_mulVec,dotProduct_sub,vecMulVec_mulVec,op_smul_eq_smul,dotProduct_smul,smul_eq_mul]
  have sym : u ⬝ᵥ (A*ᵥy) = (A*ᵥu) ⬝ᵥ y := by
    rw [dotProduct_mulVec,←mulVec_transpose]
    have es : Aᵀ=A := by ext i j;exact h.isHermitian.apply i j
    rw [es]
  let c := (v ⬝ᵥ y)/w
  have test := h.dotProduct_mulVec_nonneg (y-c•u)
  simp only [star_trivial,mulVec_sub,mulVec_smul,sub_dotProduct,dotProduct_sub,dotProduct_smul,
    smul_dotProduct,smul_eq_mul,sym,hv] at test
  simp only [show y ⬝ᵥ v=v ⬝ᵥ y from dotProduct_comm _ _,
    show u ⬝ᵥ v=w from (dotProduct_comm u v).trans hu] at test
  rw [show y ⬝ᵥ v=v ⬝ᵥ y from dotProduct_comm _ _]
  have ec : c*w=v ⬝ᵥ y := by dsimp [c];field_simp
  nlinarith only [test,congrArg (fun z:ℝ => z*(v ⬝ᵥ y)) ec,congrArg (fun z:ℝ => z^2) ec]

private lemma sum_col_outer {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℝ) :
    (∑ j,vecMulVec (Vᵀ j) (Vᵀ j)) = V*Vᵀ := by
  ext a b;simp [Matrix.sum_apply,Matrix.mul_apply,vecMulVec_apply]

private lemma forward {n m : ℕ} (A : Fin m → Mat n) (u : Vec n) (h : admissible A u) :
    eligible (output A u) := by
  classical
  let V := cols A u
  let P := ∑ j,A j
  let w := weight A u
  have hP : P.PosDef := h.2.1
  let : Invertible (1:Mat m) := invertibleOne
  let : Invertible P := hP.isUnit.invertible
  have hsum : (P-V*Vᵀ).PosSemidef := by
    rw [←sum_col_outer]
    change ((∑ j,A j) - ∑ j,vecMulVec (Vᵀ j) (Vᵀ j)).PosSemidef
    rw [←sum_sub_distrib]
    apply Matrix.posSemidef_sum
    intro j _
    exact col_minorant (A j) (h.1 j) u (Vᵀ j) (w j) (col_cond h j).1 (col_cond h j).2.1 (col_cond h j).2.2
  have hup : (1 - Vᵀ*P⁻¹*V).PosSemidef := by
    have H := (PosDef.fromBlocks₂₂ P V (D:=1) (by simpa using (PosDef.one : (1:Mat m).PosDef))).2 (by simpa using hsum)
    simpa using (PosDef.fromBlocks₁₁ V (1:Mat m) hP).1 H
  have hwu : V*ᵥw = P*ᵥu := by
    rw [show P*ᵥu = ∑ j, A j *ᵥ u by simp [P,Matrix.sum_mulVec]]
    funext i
    simp only [Matrix.mulVec, dotProduct,Finset.sum_apply]
    exact sum_congr rfl fun j _ => by
      have H := congrFun (col_cond h j).2.1 i
      simpa [V,w,Matrix.mulVec,dotProduct,mul_comm] using H.symm
  have hinv : P⁻¹*P=1 := Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_invertible P)
  refine ⟨?_,hup,w,fun j => (col_cond h j).1,?_⟩
  · simpa [output,V,P] using hP.inv.posSemidef.conjTranspose_mul_mul_same V
  · change (Vᵀ*P⁻¹*V)*ᵥw=w
    rw [←mulVec_mulVec,hwu,←mulVec_mulVec (P*ᵥu) Vᵀ P⁻¹,mulVec_mulVec u P⁻¹ P,hinv,one_mulVec]
    funext j;exact (col_cond h j).2.2
open scoped MatrixOrder Matrix.Norms.L2Operator
private lemma realize {m : ℕ} (hm : 0 < m) (B : Mat m) (h : eligible B) :
    ∃ (A : Fin m → Mat m) (u : Vec m), admissible A u ∧ (∑ j,A j)=1 ∧ output A u=B := by
  classical
  obtain ⟨hB,h1,w,hw,hBw⟩ := h
  obtain ⟨V,hV⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  have hv : B=Vᵀ*V := hV
  let : Invertible (1:Mat m) := invertibleOne
  let R := 1-V*Vᵀ
  have hr : R.PosSemidef := by
    have H := (PosDef.fromBlocks₁₁ V (1:Mat m) (PosDef.one : (1:Mat m).PosDef)).2 (by simpa [hv] using h1)
    simpa [R] using (PosDef.fromBlocks₂₂ (1:Mat m) V (PosDef.one : (1:Mat m).PosDef)).1 H
  let u := V*ᵥw
  have hwu : Vᵀ*ᵥu=w := by rw [show u=V*ᵥw from rfl,mulVec_mulVec,←hv,hBw]
  have hRu : R*ᵥu=0 := by
    dsimp only [R]
    rw [sub_mulVec,one_mulVec,←mulVec_mulVec,hwu,show V*ᵥw=u from rfl,sub_self]
  let j₀ : Fin m := ⟨0,hm⟩
  let A (j : Fin m) : Mat m := vecMulVec (Vᵀ j) (Vᵀ j) + if j=j₀ then R else 0
  have hsum : ∑ j,A j=1 := by
    simp [A,sum_add_distrib,sum_col_outer,R]
  have hps (j) : (A j).PosSemidef := by
    apply PosSemidef.add
    · simpa using posSemidef_vecMulVec_self_star (Vᵀ j)
    · split_ifs <;> first | exact hr | exact PosSemidef.zero
  have key (j) : A j*ᵥu=w j•Vᵀ j := by
    have hj : (Vᵀ j) ⬝ᵥ u=w j := congrFun hwu j
    simp only [A,add_mulVec,vecMulVec_mulVec,op_smul_eq_smul,hj]
    split_ifs <;> simp [hRu]
  have quad (j) : u ⬝ᵥ (A j *ᵥu)=(w j)^2 := by
    rw [key,dotProduct_smul,smul_eq_mul,dotProduct_comm u]
    change w j*(Vᵀ*ᵥu) j=w j^2
    rw [hwu,pow_two]
  have hy (j) : weight A u j=w j := by
    rw [weight,quad,Real.sqrt_sq (hw j).le]
  have hc : cols A u=V := by
    ext i j
    simp only [cols,key,Pi.smul_apply,smul_eq_mul,transpose_apply,hy]
    field_simp [(hw j).ne']
  refine ⟨A,u,⟨hps,hsum ▸ PosDef.one,fun j => (quad j).symm ▸ sq_pos_of_pos (hw j)⟩,hsum,?_⟩
  rw [output,hc,hsum]
  simpa using hv.symm
private lemma spectrum_bounds {m : ℕ} {B : Mat m} (hm : 0 < m) (h : eligible B) :
    IsGreatest (eigs B) 1 ∧ ∀ t∈eigs B,0 ≤ t := by
  obtain ⟨hB,hD,w,hw,he⟩ := h
  have w0 : w ≠ 0 := by
    intro Hz
    have hn := hw ⟨0,hm⟩
    simp [Hz] at hn
  have hb {t} (ht : t∈eigs B) : 0 ≤ t ∧ t ≤ 1 := by
    obtain ⟨v,hv,hev⟩ := ht
    have h₁ := hB.dotProduct_mulVec_nonneg v
    have h₂ := hD.dotProduct_mulVec_nonneg v
    have hp : 0 < v ⬝ᵥ v := (dotProduct_star_self_pos_iff.mpr hv)
    simp only [star_trivial,sub_mulVec,one_mulVec,hev,dotProduct_sub,dotProduct_smul,smul_eq_mul] at h₁ h₂
    exact ⟨nonneg_of_mul_nonneg_left h₁ hp,by nlinarith⟩
  exact ⟨⟨⟨w,w0,by simpa using he⟩,fun _ ht => (hb ht).2⟩,fun _ ht => (hb ht).1⟩
end OMA.S_mo_345027
open OMA.S_mo_345027
theorem OMA.solution : type_of% @OMA.S_mo_345027.main := by
  constructor
  · intro m n A u hm h
    exact ⟨forward A u h,spectrum_bounds hm (forward A u h)⟩
  · intro m B hm
    refine ⟨realize hm B,?_⟩
    rintro ⟨A,u,ha,_,rfl⟩
    exact forward A u ha
