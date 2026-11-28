import OMAStatements.S_mo_156854

namespace OMA.S_mo_156854
open Matrix
open scoped NNReal
variable {ι κ : Type*} [Fintype ι]
lemma entry_le_peak (B : Matrix ι κ ℝ) (i : ι) (j : κ) : B i j^2 ≤ coordPeak B j := by
  have h := Finset.le_sup (s:=Finset.univ) (f:=fun i => ‖B i j‖₊^2) (Finset.mem_univ i)
  simpa [coordPeak,Real.norm_eq_abs] using (NNReal.coe_le_coe.mpr h)
lemma row_le_lev [Fintype κ] (B : Matrix ι κ ℝ) (i : ι) : ∑ j,B i j^2 ≤ leverage B := by
  have h := Finset.le_sup (s:=Finset.univ) (f:=fun i => ∑ j,‖B i j‖₊^2) (Finset.mem_univ i)
  simpa [leverage,NNReal.coe_sum,Real.norm_eq_abs] using (NNReal.coe_le_coe.mpr h)
lemma lev_le [Fintype κ] (B : Matrix ι κ ℝ) {a : ℝ} (ha : 0≤a) (h : ∀ i,∑ j,B i j^2≤a) : leverage B≤a := by
  lift a to ℝ≥0 using ha
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  simpa [NNReal.coe_sum,Real.norm_eq_abs] using h i
lemma peak_le (B : Matrix ι κ ℝ) (j : κ) {a : ℝ} (ha : 0≤a) (h : ∀ i,B i j^2≤a) : coordPeak B j≤a := by
  lift a to ℝ≥0 using ha
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  simpa [Real.norm_eq_abs] using h i
lemma cost_bounds [Fintype κ] (B : Matrix ι κ ℝ) : leverage B≤cost B ∧ cost B ≤ Fintype.card κ * leverage B := by
  have hp (j : κ) : 0≤coordPeak B j := NNReal.coe_nonneg _
  constructor
  · exact lev_le B (Finset.sum_nonneg fun j _ => hp j) (fun i => Finset.sum_le_sum fun j _ => entry_le_peak B i j)
  · calc cost B ≤ ∑ _ : κ,leverage B := Finset.sum_le_sum fun j _ => peak_le B j (NNReal.coe_nonneg _) fun i =>
          (Finset.single_le_sum (f:=fun j => B i j^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans (row_le_lev B i)
         _ = _ := by simp
end OMA.S_mo_156854

namespace OMA.S_mo_156854
open Matrix Set
open scoped RealInnerProductSpace

private lemma net_basis {d : ℕ} (i₀ : Fin d) (x : EuclideanSpace ℝ (Fin d)) (hx : ‖x‖=1) :
    ∃ O : Matrix (Fin d) (Fin d) ℝ, Oᵀ*O=1 ∧ ∀ j, O i₀ j=x j := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let L := (ℝ ∙ (b i₀-x))ᗮ.reflection
  have hl : L (b i₀)=x := Submodule.reflection_sub ((b.orthonormal.norm_eq_one i₀).trans hx.symm)
  let O : Matrix (Fin d) (Fin d) ℝ := fun i j => L (b i) j
  refine ⟨O,mul_eq_one_comm.mp ?_,fun j => congrArg (fun y : EuclideanSpace ℝ (Fin d) => y j) hl⟩
  ext i j
  change (∑ k, L (b i) k * L (b j) k) = (1 : Matrix (Fin d) (Fin d) ℝ) i j
  have h := (L.inner_map_map (b j) (b i)).trans (orthonormal_iff_ite.mp b.orthonormal j i)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  by_cases hij : i = j
  · subst j
    simpa [dotProduct] using h
  · simpa [dotProduct, Matrix.one_apply, hij, Ne.symm hij] using h

lemma spherical_net (d : ℕ) (hd : 0<d) (η : ℝ) (hη : 0<η) :
    ∃ (t : ℕ) (O : Fin t → Matrix (Fin d) (Fin d) ℝ), 0<t ∧ (∀ a, (O a)ᵀ*O a=1) ∧
      ∀ x : Fin d→ℝ, (∑ j, (x j)^2)=1 → ∃ a, 1-η ≤ (∑ j, O a ⟨0,hd⟩ j * x j)^2 := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let S := Metric.sphere (0:E) 1
  let i₀ : Fin d := ⟨0,hd⟩
  let cap (z : S) : Set E := {x | 1-η < ⟪(z:E),x⟫^2}
  have hzn (z : S) : ‖(z:E)‖=1 := by simpa only [S,Metric.mem_sphere,dist_zero_right] using z.prop
  have hop (z : S) : IsOpen (cap z) := isOpen_lt continuous_const (by fun_prop)
  have hcover : S ⊆ ⋃ z : S,cap z := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x,hx⟩,?_⟩
    change 1-η<⟪x,x⟫^2
    rw [real_inner_self_eq_norm_sq,hzn ⟨x,hx⟩]
    linarith
  obtain ⟨F,hF⟩ := (isCompact_sphere (0:E) 1).elim_finite_subcover cap hop hcover
  have pick (x : E) (hx : x∈S) : ∃ z : F, 1-η<⟪(z.val:E),x⟫^2 := by
    obtain ⟨z,hz⟩:=mem_iUnion.mp (hF hx)
    obtain ⟨hf,hc⟩:=mem_iUnion.mp hz
    exact ⟨⟨z,hf⟩,hc⟩
  let x₀ : E := EuclideanSpace.basisFun (Fin d) ℝ i₀
  have hx₀ : x₀∈S := by simpa only [S,Metric.mem_sphere,dist_zero_right,x₀] using (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.norm_eq_one i₀
  obtain ⟨z,_⟩:=pick x₀ hx₀
  have hv (a : F) := net_basis i₀ (a.val:E) (hzn a.val)
  choose Q hQ hr using hv
  let e := Fintype.equivFin F
  refine ⟨_,fun a => Q (e.symm a),Fintype.card_pos_iff.mpr ⟨z⟩,fun a => hQ _,?_⟩
  intro x hx
  let y : E := WithLp.toLp 2 x
  have hy : y ∈ S := by
    have hyy : ⟪y,y⟫=1 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simpa only [y,dotProduct,WithLp.ofLp_toLp,Pi.star_apply,star_trivial,pow_two] using hx
    rw [real_inner_self_eq_norm_sq] at hyy
    have hnorm : ‖y‖=1 := by nlinarith [norm_nonneg y]
    simpa [S,Metric.mem_sphere] using hnorm
  obtain ⟨a,ha⟩:=pick y hy
  refine ⟨e a,?_⟩
  change 1-η≤(∑ j, Q (e.symm (e a)) i₀ j * x j)^2
  rw [e.symm_apply_apply]
  simp_rw [hr]
  change 1-η < inner ℝ (a.val : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 x) ^ 2 at ha
  rw [EuclideanSpace.inner_eq_star_dotProduct] at ha
  simpa only [dotProduct, WithLp.ofLp_toLp, Pi.star_apply, star_trivial, mul_comm] using ha.le

end OMA.S_mo_156854

namespace OMA.S_mo_156854
open Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
lemma same_projection (B W : Matrix ι κ ℝ) (hB : Bᵀ*B=1) (hW : Wᵀ*W=1)
    (hr : LinearMap.range W.mulVecLin = LinearMap.range B.mulVecLin) : W*Wᵀ=B*Bᵀ := by
  have hmat : (B*Bᵀ)*W=W := by
    ext i j
    have hcol : W.col j ∈ LinearMap.range W.mulVecLin := ⟨Pi.single j 1,W.mulVec_single_one j⟩
    rw [hr] at hcol
    obtain ⟨x,hx⟩ := hcol
    change B *ᵥ x=W.col j at hx
    have he : (B*Bᵀ) *ᵥ (W.col j)=W.col j := by
      rw [←hx,mulVec_mulVec,Matrix.mul_assoc,hB,Matrix.mul_one]
    exact congrFun he i
  let Q := Bᵀ*W
  have hq : B*Q=W := by simpa [Q,←Matrix.mul_assoc] using hmat
  have horth : Qᵀ*Q=1 := by
    change (Bᵀ*W)ᵀ*(Bᵀ*W)=1
    rw [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
    change Wᵀ*(B*Q)=1
    rw [hq,hW]
  have hleft := mul_eq_one_comm.mp horth
  calc W*Wᵀ = (B*Q)*(B*Q)ᵀ := by rw [hq]
       _ = B*(Q*Qᵀ)*Bᵀ := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
       _ = _ := by rw [hleft,Matrix.mul_one]
lemma projection_coord (B : Matrix ι κ ℝ) (hB : Bᵀ*B=1) (i : ι) :
    ∑ l,((B*Bᵀ) l i)^2=∑ j,B i j^2 := by
  have h : (B*Bᵀ)ᵀ*(B*Bᵀ)=B*Bᵀ := by
    rw [Matrix.transpose_mul,Matrix.transpose_transpose,←Matrix.mul_assoc,Matrix.mul_assoc B Bᵀ B,hB,Matrix.mul_one]
  have hh := congrArg (fun M : Matrix ι ι ℝ => M i i) h
  change (∑ l,(B*Bᵀ) l i*(B*Bᵀ) l i)=∑ j,B i j*B i j at hh
  simpa only [pow_two] using hh
end OMA.S_mo_156854

namespace OMA.S_mo_156854
open Matrix
private noncomputable def stacked {t d : ℕ} (a : ℝ) (O : Fin t → Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin t × Fin d) (Fin d) ℝ := .of fun i j => a*O i.1 i.2 j
private lemma stack_iso {t d : ℕ} {a : ℝ} (hscale : (t:ℝ)*a^2=1) (O : Fin t → Matrix (Fin d) (Fin d) ℝ)
    (ho : ∀ k,(O k)ᵀ*O k=1) : (stacked a O)ᵀ*(stacked a O)=1 := by
  ext i j
  change ∑ kl : Fin t × Fin d, (a*O kl.1 kl.2 i)*(a*O kl.1 kl.2 j) = _
  rw [Fintype.sum_prod_type]
  calc ∑ k,∑ l,(a*O k l i)*(a*O k l j) = ∑ k,a^2*((O k)ᵀ*O k) i j := by
         apply Finset.sum_congr rfl
         intro k _
         simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro l _
         ring
       _ = _ := by simp only [ho,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
                   rw [←mul_assoc,hscale,one_mul]
private lemma stack_lev {t d : ℕ} {a : ℝ} (ht : 0<t) (hd : 0<d) (O : Fin t → Matrix (Fin d) (Fin d) ℝ)
    (ho : ∀ k,(O k)ᵀ*O k=1) : leverage (stacked a O)=a^2 := by
  have eqr (i : Fin t × Fin d) : ∑ j,(stacked a O i j)^2=a^2 := by
    have hor := mul_eq_one_comm.mp (ho i.1)
    have hdiag := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i.2 i.2) hor
    change ∑ j,(a*O i.1 i.2 j)^2=a^2
    simp only [mul_pow,← Finset.mul_sum]
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,←pow_two] at hdiag
    rw [hdiag,mul_one]
  exact le_antisymm (lev_le _ (sq_nonneg _) fun i => (eqr i).le)
    ((eqr (⟨0,ht⟩,⟨0,hd⟩)).symm.le.trans (row_le_lev _ _))
lemma all_bases {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B W : Matrix ι κ ℝ) (hW : Wᵀ*W=1) (hP : W*Wᵀ=B*Bᵀ) :
    ∃ Q : Matrix κ κ ℝ,Qᵀ*Q=1 ∧ B*Q=W := by
  have he : B*(Bᵀ*W)=W := by rw [←Matrix.mul_assoc,←hP,Matrix.mul_assoc,hW,Matrix.mul_one]
  refine ⟨Bᵀ*W,?_,he⟩
  rw [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc,he,hW]
end OMA.S_mo_156854

namespace OMA.S_mo_156854
open Matrix
lemma frame_from_net {d t : ℕ} (hd : 0<d) (ht : 0<t) (η : ℝ)
    (O : Fin t → Matrix (Fin d) (Fin d) ℝ) (ho : ∀ a,(O a)ᵀ*O a=1)
    (hn : ∀ x : Fin d→ℝ, (∑ j,(x j)^2)=1 → ∃ a,1-η ≤ (∑ j,O a ⟨0,hd⟩ j*x j)^2) :
    ∃ B : Matrix (Fin t × Fin d) (Fin d) ℝ, Bᵀ*B=1 ∧ 0<leverage B ∧
      ∀ W : Matrix (Fin t × Fin d) (Fin d) ℝ, Wᵀ*W=1 → W*Wᵀ=B*Bᵀ →
        (1-η)*(d:ℝ)*leverage B ≤ cost W := by
  let a := (Real.sqrt t)⁻¹
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have ha : 0<a := inv_pos.mpr (Real.sqrt_pos.mpr ht')
  have hscale : (t:ℝ)*a^2=1 := by simp [a,inv_pow,Real.sq_sqrt ht'.le,ht'.ne']
  have hlev := stack_lev (a:=a) ht hd O ho
  refine ⟨stacked a O,stack_iso hscale O ho,hlev.symm ▸ (sq_pos_of_pos ha),?_⟩
  intro W hW hP
  obtain ⟨Q,hQ,rfl⟩ := all_bases _ W hW hP
  rw [hlev]
  have hpeak (j : Fin d) : a^2*(1-η) ≤ coordPeak (stacked a O*Q) j := by
    have hcol := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M j j) hQ
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,←pow_two] at hcol
    obtain ⟨k,hk⟩ := hn (fun i => Q i j) hcol
    have he : (stacked a O*Q) (k,⟨0,hd⟩) j=a*(∑ i,O k ⟨0,hd⟩ i*Q i j) := by
      simp [Matrix.mul_apply,stacked,Finset.mul_sum,mul_assoc]
    apply (mul_le_mul_of_nonneg_left hk (sq_nonneg a)).trans
    rw [←mul_pow,←he]
    exact entry_le_peak _ _ _
  have hsum := Finset.sum_le_sum (s:=Finset.univ) fun j _ => hpeak j
  calc (1-η)*(d:ℝ)*a^2 = ∑ _ : Fin d,a^2*(1-η) := by simp; ring
       _ ≤ _ := hsum
end OMA.S_mo_156854

open OMA.S_mo_156854
theorem OMA.solution : type_of% @OMA.S_mo_156854.main := by
  refine ⟨fun _ _ _ _ => cost_bounds,fun _ _ _ _ _ => projection_coord,?_⟩
  intro d hd η hη
  obtain ⟨t,O,ht,ho,hn⟩ := spherical_net d hd η hη
  obtain ⟨B,hB,hpos,hcost⟩ := frame_from_net hd ht η O ho hn
  exact ⟨t,ht,B,hB,hpos,fun W hW hr => hcost W hW (same_projection B W hB hW hr)⟩
