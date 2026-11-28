import OMAStatements.S_mo_187427

namespace OMA.S_mo_187427
open Matrix Finset
private lemma gram_det {n d} (U V : Rect n d) (hu : frame U) (hv : frame V) :
    ((fromCols U V)ᵀ*(fromCols U V)).det=(1-(Uᵀ*V)*(Vᵀ*U)).det := by
  rw [transpose_fromCols,fromRows_mul_fromCols,hu,hv,det_fromBlocks_one₂₂]

private lemma small_gap {n d} (hn : n<2*d) (U V : Rect n d) (hu : frame U) (hv : frame V) : gap U V=0 := by
  let H := fromCols U V
  have hz : (Hᵀ*H).det=0 := by
    by_contra hc
    have he := rank_of_isUnit (Hᵀ*H) ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hc))
    have hb := (rank_mul_le_right Hᵀ H).trans (rank_le_card_height H)
    rw [he] at hb
    simp at hb
    omega
  rw [gap,←gram_det U V hu hv,hz,Real.sqrt_zero]

private lemma apart_of_pos {n d} {U V : Rect n d} (hu : frame U) (hv : frame V) (h : 0<gap U V) : apart U V := by
  let H := fromCols U V
  have hdet : (Hᵀ*H).det≠0 := by
    rw [gram_det U V hu hv]
    exact (Real.sqrt_pos.mp h).ne'
  have hin := Matrix.mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  apply Submodule.disjoint_def.mpr
  rintro z ⟨x,hx⟩ ⟨y,hy⟩
  change U *ᵥ x=z at hx
  change V *ᵥ y=z at hy
  have hxy : H *ᵥ Sum.elim x (-y)=0 := by rw [fromCols_mulVec_sumElim,Matrix.mulVec_neg,hx,hy,add_neg_cancel]
  have ht : Sum.elim x (-y)=0 := hin (by rw [←Matrix.mulVec_mulVec, hxy,Matrix.mulVec_zero,Matrix.mulVec_zero])
  have hxx : x=0 := funext fun i => congrFun ht (Sum.inl i)
  rw [←hx,hxx,Matrix.mulVec_zero]

open scoped Matrix.Norms.Frobenius

private lemma line_frobenius {n} (U V : Rect n 1) (hu : frame U) (hv : frame V) :
    ‖U*Uᵀ-V*Vᵀ‖ = Real.sqrt 2 * gap U V := by
  let u (i : Fin n) := U i 0
  let v (i : Fin n) := V i 0
  let a := ∑ i, u i*v i
  have hn (P : Rect n 1) (hP : frame P) : ∑ i, (P i 0)^2=1 := by
    have h := congrFun (congrFun hP 0) 0
    simpa [Matrix.mul_apply,pow_two] using h
  have huu : ∑ i, (u i)^2=1 := hn U hu
  have hvv : ∑ i, (v i)^2=1 := hn V hv
  have hcross (x y : Fin n → ℝ) :
      (∑ i,∑ j,(x i*x j)*(y i*y j))=(∑ i,x i*y i)^2 := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsum : (∑ i,∑ j,(u i*u j-v i*v j)^2)=2*(1-a^2) := by
    simp_rw [show ∀ i j, (u i*u j-v i*v j)^2 =
      (u i*u j)*(u i*u j)+(v i*v j)*(v i*v j)-2*((u i*u j)*(v i*v j)) by intros; ring]
    simp only [sum_sub_distrib,sum_add_distrib,←Finset.mul_sum]
    rw [hcross u u,hcross v v,hcross u v]
    simp only [←sq,huu,hvv,a]
    ring
  have hnorm : ‖U*Uᵀ-V*Vᵀ‖ = Real.sqrt (∑ i,∑ j,(u i*u j-v i*v j)^2) := by
    rw [Matrix.frobenius_norm_def,Real.sqrt_eq_rpow]
    simp [Matrix.mul_apply,Real.norm_eq_abs,sq_abs,u,v]
  have hgap : gap U V=Real.sqrt (1-a^2) := by
    rw [gap,Matrix.det_eq_elem_of_subsingleton _ 0]
    congr 1
    simp only [Matrix.sub_apply,Matrix.one_apply_eq,Matrix.mul_apply,Fin.sum_univ_one,Matrix.transpose_apply]
    rw [show (∑ i, V i 0*U i 0)=a by dsimp [a,u,v];simp_rw [mul_comm]]
    change 1-a*a=1-a^2
    ring
  rw [hnorm,hsum,hgap,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]

private lemma line_triangle (n : ℕ) : triangle n 1 := by
  intro U V W hu hv hw
  have h := dist_triangle (U*Uᵀ) (V*Vᵀ) (W*Wᵀ)
  simp only [dist_eq_norm] at h
  rw [line_frobenius U W hu hw,line_frobenius U V hu hv,line_frobenius V W hv hw,←mul_add] at h
  exact (le_of_mul_le_mul_left h (Real.sqrt_pos.mpr (by norm_num)))

private def paired {n d m : ℕ} (e : Fin n ≃ (Fin d ⊕ (Fin d ⊕ Fin m))) (a b : Fin d→ℝ) : Rect n d :=
  (fromRows (diagonal a) (fromRows (diagonal b) (0 : Rect m d))).submatrix e id

private lemma paired_gram {n d m} (e : Fin n ≃ (Fin d ⊕ (Fin d ⊕ Fin m))) (a b c f : Fin d→ℝ) :
    (paired e a b)ᵀ*paired e c f=diagonal (fun j => a j*c j+b j*f j) := by
  simp only [paired,transpose_submatrix,submatrix_mul_equiv,submatrix_id_id,transpose_fromRows,
    diagonal_transpose,transpose_zero,fromCols_mul_fromRows,Matrix.zero_mul,add_zero,diagonal_mul_diagonal,
    diagonal_add]

private lemma gap_diagonal {n d} (U V : Rect n d) (a b : Fin d→ℝ) (h : Uᵀ*V=diagonal a)
    (hab : ∀ i, 1-(a i)^2=(b i)^2) (hb : ∀ i,0≤b i) : gap U V=∏ i,b i := by
  have h' : Vᵀ*U=diagonal a := by simpa using congrArg transpose h
  rw [gap,h,h',diagonal_mul_diagonal,← diagonal_one,diagonal_sub,det_diagonal]
  have he (i : Fin d) : (1-(a i*a i))=(b i)^2 := by simpa only [pow_two] using hab i
  change Real.sqrt (∏ i, (1-a i*a i))=_
  simp_rw [he]
  rw [Finset.prod_pow,Real.sqrt_sq (Finset.prod_nonneg (fun i _ => hb i))]

private lemma examples (n d : ℕ) (hd : 2≤d) (hn : 2*d≤n) (ε : ℝ) (he : 0<ε) :
    ∃ U V W : Rect n d, frame U ∧ frame V ∧ frame W ∧ apart U V ∧ apart V W ∧ apart U W ∧
      gap U W=1 ∧ 0<gap U V ∧ 0<gap V W ∧ gap U V+gap V W<ε := by
  classical
  let e : Fin n ≃ (Fin d ⊕ (Fin d ⊕ Fin (n-2*d))) := Fintype.equivOfCardEq (by simp;omega)
  let t := min (ε/4) (1/4)
  have ht : 0<t := lt_min (by positivity) (by norm_num)
  have ht₁ : t≤1/4 := min_le_right _ _
  have htε : t≤ε/4 := min_le_left _ _
  let s := Real.sqrt (1-t^2)
  have hrad : 0<1-t^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht₁) (by linarith : 0≤1/4+t)]
  have hs : 0<s := Real.sqrt_pos.mpr hrad
  have hsq : s^2=1-t^2 := Real.sq_sqrt hrad.le
  have hs₁ : s≤1 := by nlinarith [sq_nonneg t]
  let z : Fin d := ⟨0,by omega⟩
  let j : Fin d := ⟨1,by omega⟩
  have hj : j ≠ z := by intro h; have := congrArg Fin.val h; contradiction
  let a (i : Fin d) := if i=z then s else t
  let b (i : Fin d) := if i=z then t else s
  have hab (i : Fin d) : a i^2+b i^2=1 := by dsimp only [a,b];split <;> linarith
  have ha (i) : 0<a i := by dsimp only [a];split <;> assumption
  have hb (i) : 0<b i := by dsimp only [b];split <;> assumption
  have ha₁ (i) : a i≤1 := by dsimp only [a];split <;> linarith
  have hb₁ (i) : b i≤1 := by dsimp only [b];split <;> linarith
  let U := paired e 1 0
  let W := paired e 0 1
  let V := paired e a b
  have hu : frame U := by simp [frame,U,paired_gram]
  have hw : frame W := by simp [frame,W,paired_gram]
  have hv : frame V := by
    change (paired e a b)ᵀ*paired e a b=1
    rw [paired_gram]
    simp_rw [←sq,hab]
    exact diagonal_one
  have hUV : gap U V=∏ i,b i := gap_diagonal _ _ a b (by simp [U,V,paired_gram])
    (fun i => by linarith [hab i]) (fun i => (hb i).le)
  have hVW : gap V W=∏ i,a i := gap_diagonal _ _ b a (by simp [V,W,paired_gram])
    (fun i => by linarith [hab i]) (fun i => (ha i).le)
  have hUW : gap U W=1 := by simp [gap,U,W,paired_gram]
  have hpos₁ : 0<gap U V := hUV ▸ prod_pos (fun i _ => hb i)
  have hpos₂ : 0<gap V W := hVW ▸ prod_pos (fun i _ => ha i)
  have bound (f : Fin d→ℝ) (hp : ∀ i,0<f i) (hq : ∀ i,f i≤1) (i) : (∏ k,f k)≤f i := by
    simpa using (prod_le_prod_of_subset_of_le_one (subset_univ ({i}:Finset (Fin d)))
      (fun j _ => (hp j).le) (fun j _ _ => hq j))
  refine ⟨U,V,W,hu,hv,hw,apart_of_pos hu hv hpos₁,apart_of_pos hv hw hpos₂,
    apart_of_pos hu hw (by rw [hUW];norm_num),hUW,hpos₁,hpos₂,?_⟩
  have hl := bound b hb hb₁ z
  have hr := bound a ha ha₁ j
  simp only [b,if_pos rfl] at hl
  simp only [a,if_neg hj] at hr
  rw [hUV,hVW]
  change (∏ i,b i)≤t at hl
  change (∏ i,a i)≤t at hr
  linarith

end OMA.S_mo_187427
open OMA.S_mo_187427

theorem OMA.solution : type_of% @OMA.S_mo_187427.main := by
  refine ⟨?_,examples⟩
  intro n d
  constructor
  · intro h
    by_contra! hn
    obtain ⟨U,V,W,hu,hv,hw,_,_,_,hUW,_,_,hsmall⟩ := examples n d (by omega) hn.2 1 zero_lt_one
    have ht := h U V W hu hv hw
    linarith
  · rintro (hd|hn)
    · interval_cases d
      · intro U V W hu hv hw
        simp [gap]
      · exact line_triangle n
    · intro U V W hu hv hw
      rw [small_gap hn U W hu hw,small_gap hn U V hu hv,small_gap hn V W hv hw,add_zero]
