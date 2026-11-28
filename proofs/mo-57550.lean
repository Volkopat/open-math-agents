import OMAStatements.S_mo_57550

namespace OMA.S_mo_57550
open Matrix
open scoped Matrix.Norms.L2Operator
private theorem entry_sq (R : Three) (hR : rotation R) (i j : Fin 3) : (R i j)^2 ≤ 1 := by
  have c : (∑ k, R k j * R k j) = 1 := calc
    _ = (Rᵀ*R) j j := rfl
    _ = (1 : Three) j j := congrArg (fun M : Three => M j j) hR.1
    _ = 1 := Matrix.one_apply_eq _
  rw [←c]
  simpa [pow_two] using Finset.single_le_sum
    (f := fun k : Fin 3 => R k j * R k j) (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
theorem rotation_compact : IsCompact {R : Three | rotation R} := by
  have closed : IsClosed {R : Three | rotation R} :=
    (isClosed_eq (show Continuous (fun R : Three => Rᵀ*R) by fun_prop) continuous_const).inter
      (isClosed_eq (show Continuous (fun R : Three => R.det) by fun_prop) continuous_const)
  have box : IsCompact (Set.Icc (fun _ _ : Fin 3 => (-1:ℝ)) (fun _ _ : Fin 3 => (1:ℝ))) :=
    isCompact_Icc
  refine box.of_isClosed_subset closed ?_
  intro R hR
  have hentry (i j : Fin 3) : |R i j| ≤ 1 := by
    have h := entry_sq R hR i j
    exact (sq_le_one_iff_abs_le_one _).mp h
  exact ⟨fun i j => (abs_le.mp (hentry i j)).1, fun i j => (abs_le.mp (hentry i j)).2⟩

theorem attained {m n : ℕ} (A : Matrix (Fin m) (Fin n × Fin 3) ℝ)
    (v : Fin n → Fin 3 → ℝ) :
    ∃ R, rotation R ∧ ∀ S, rotation S → objective A v S ≤ objective A v R := by
  have hb : Continuous (fun R : Three => blockProduct A v R) := by
    apply continuous_matrix
    intro t j
    simp only [blockProduct, of_apply]
    fun_prop
  have hobj : Continuous (objective A v) := by
    change Continuous (fun R => ‖blockProduct A v R‖)
    exact hb.norm
  have hne : ({R : Three | rotation R} : Set Three).Nonempty :=
    ⟨1,by simp [rotation]⟩
  exact rotation_compact.exists_isMaxOn hne hobj.continuousOn
end OMA.S_mo_57550

namespace OMA.S_mo_57550
open Matrix
theorem trace_pair {m n : ℕ} (A : Matrix (Fin m) (Fin n × Fin 3) ℝ)
    (v : Fin n → Fin 3 → ℝ) (R : Three) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    (Rᵀ * coefficient A v x y).trace = ∑ t, ∑ j, y t * blockProduct A v R t j * x j := by
  classical
  simp only [trace, diag_apply, mul_apply, transpose_apply, coefficient, blockProduct, of_apply,
    Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ b : Fin 3, ∑ a : Fin 3, ∑ t : Fin m, ∑ j : Fin n,
          y t * (A t (j,a) * (R a b * v j b)) * x j := by
      congr! 4 with b a t j
      ring
    _ = _ := by
      conv_lhs => rw [Finset.sum_comm]
      conv_lhs => enter [2,a]; rw [Finset.sum_comm]
      conv_lhs => rw [Finset.sum_comm]
      congr! 1 with t
      conv_lhs => enter [2,a]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
end OMA.S_mo_57550

namespace OMA.S_mo_57550
open Matrix Finset Module Unitary
open scoped InnerProductSpace

private lemma real_svd_three (C : Three) :
    ∃ U V : unitary Three, C=(U:Three)*diagonal (fun i : Fin 3 => C.toEuclideanLin.singularValues i.val)*(V:Three)ᵀ := by
  classical
  let T := C.toEuclideanLin
  let S := T.adjoint.comp T
  let hs : S.IsSymmetric := T.isSymmetric_adjoint_comp_self
  let hd : finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  let b := hs.eigenvectorBasis hd
  let s (j : Fin 3) := T.singularValues j.val
  let v (j : Fin 3) := T (b j)
  have hv (j : Fin 3) : ‖v j‖=s j := by
    apply (sq_eq_sq₀ (norm_nonneg _) (T.singularValues_nonneg _)).mp
    change ‖T (b j)‖^2=(T.singularValues j.val)^2
    rw [T.sq_singularValues_fin hd j,←real_inner_self_eq_norm_sq,← LinearMap.adjoint_inner_left]
    change ⟪S (b j), b j⟫_ℝ = _
    rw [hs.apply_eigenvectorBasis hd j,real_inner_smul_left,real_inner_self_eq_norm_sq,b.orthonormal.norm_eq_one]
    simp
  have ho (i j : Fin 3) (hij : i≠j) : ⟪v i,v j⟫_ℝ=0 := by
    change ⟪T (b i),T (b j)⟫_ℝ=0
    rw [← LinearMap.adjoint_inner_left]
    change ⟪S (b i),b j⟫_ℝ=0
    rw [hs.apply_eigenvectorBasis hd i,real_inner_smul_left,b.orthonormal.inner_eq_zero hij,mul_zero]
  let f := fun i : Fin 3 => (‖v i‖⁻¹ : ℝ) • v i
  let I : Set (Fin 3) := {i | v i ≠ 0}
  have hf : Orthonormal ℝ (I.domRestrict f) := by
    constructor
    · rintro ⟨i,hi⟩
      change ‖(‖v i‖⁻¹ : ℝ) • v i‖=1
      rw [norm_smul_of_nonneg (by positivity),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hi)]
    · intro i j hij
      change ⟪(‖v i.val‖⁻¹:ℝ) • v i.val,(‖v j.val‖⁻¹:ℝ) • v j.val⟫_ℝ=0
      rw [real_inner_smul_left,real_inner_smul_right,ho _ _ (fun h => hij (Subtype.ext h))]
      ring
  obtain ⟨u,hu⟩ := hf.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let U : unitary Three := ⟨(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix u.toBasis,
    (EuclideanSpace.basisFun (Fin 3) ℝ).toMatrix_orthonormalBasis_mem_unitary u⟩
  let V : unitary Three := ⟨(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin 3) ℝ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hcol (j : Fin 3) : s j • u j = T (b j) := by
    change s j • u j=v j
    rw [←hv]
    by_cases hj : v j=0
    · simp [hj]
    · rw [hu j hj]
      dsimp only [f]
      rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hj),one_smul]
  have hmat : (U:Three)*diagonal s = C*(V:Three) := by
    ext i j
    rw [Matrix.mul_diagonal]
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x i) (hcol j)
    change u j i * s j = ∑ k, C i k * (b j) k
    simpa [T,PiLp.smul_apply,mul_comm,Matrix.toLpLin_apply,Matrix.mulVec,dotProduct] using hh
  refine ⟨U,V,?_⟩
  change C = (U:Three)*diagonal s*(V:Three)ᵀ
  rw [hmat,Matrix.mul_assoc,show (V:Three)*(V:Three)ᵀ=1 from V.2.2,Matrix.mul_one]

lemma procrustes (C : Three) : (∀ R, rotation R → |(Rᵀ*C).trace|≤nuclear C) ∧
    ∃ R, rotation R ∧ |(Rᵀ*C).trace|=nuclear C := by
  classical
  obtain ⟨U,V,hC⟩ := real_svd_three C
  let s := fun i : Fin 3 => C.toEuclideanLin.singularValues i.val
  have hpos (i : Fin 3) : 0 ≤ s i := C.toEuclideanLin.singularValues_nonneg _
  change C=(U:Three)*diagonal s*(V:Three)ᵀ at hC
  have htrace (R : Three) : (Rᵀ*C).trace=∑ i,((V:Three)ᵀ*Rᵀ*(U:Three)) i i*s i := by
    conv_lhs => rw [hC,←Matrix.mul_assoc,trace_mul_comm]
    simp [←Matrix.mul_assoc,Matrix.trace,Matrix.mul_diagonal]
  have horth (R : Three) (hR : Rᵀ*R=1) :
      let Q := (V:Three)ᵀ*Rᵀ*(U:Three)
      Qᵀ*Q=1 := by
    dsimp only
    have hr : R*Rᵀ=1 := mul_eq_one_comm.mp hR
    have hv : (V:Three)*(V:Three)ᵀ=1 := V.2.2
    have hu : (U:Three)ᵀ*(U:Three)=1 := U.2.1
    simp only [transpose_mul,transpose_transpose,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (V:Three),hv,Matrix.one_mul,← Matrix.mul_assoc R,hr,Matrix.one_mul,hu]
  have hmax (R : Three) (hR : Rᵀ*R=1) : |(Rᵀ*C).trace|≤nuclear C := by
    let Q := (V:Three)ᵀ*Rᵀ*(U:Three)
    have hQ : Qᵀ*Q=1 := horth R hR
    rw [htrace]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    change |Q i i*s i| ≤ s i
    rw [abs_mul,abs_of_nonneg (hpos i)]
    apply mul_le_of_le_one_left (hpos i)
    have hh := congrFun (congrFun hQ i) i
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq] at hh
    have hterm := Finset.single_le_sum (s:=univ) (f:=fun j => Q j i * Q j i) (fun j _ => mul_self_nonneg _) (mem_univ i)
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩ 
  refine ⟨fun R h => hmax R h.1,?_⟩
  let O := (U:Three)*(V:Three)ᵀ
  have hUU : (U:Three)ᵀ*(U:Three)=1 := U.2.1
  have hVV : (V:Three)*(V:Three)ᵀ=1 := V.2.2
  have hVV' : (V:Three)ᵀ*(V:Three)=1 := V.2.1
  have hO : Oᵀ*O=1 := by
    dsimp [O]
    rw [transpose_mul,transpose_transpose,Matrix.mul_assoc,← Matrix.mul_assoc (U:Three)ᵀ,hUU,
      Matrix.one_mul,hVV]
  have ho : (Oᵀ*C).trace=nuclear C := by
    rw [htrace]
    have hq : (V:Three)ᵀ*Oᵀ*(U:Three)=1 := by
      dsimp [O]
      rw [transpose_mul,transpose_transpose,←Matrix.mul_assoc,hVV',Matrix.one_mul,hUU]
    simp [hq,nuclear,s]
  have hd := congrArg Matrix.det hO
  simp only [det_mul,det_transpose,det_one] at hd
  have hn : 0 ≤ nuclear C := sum_nonneg fun i _ => hpos i
  rcases mul_self_eq_one_iff.mp hd with hd | hd
  · exact ⟨O,⟨hO,hd⟩,by rw [ho,abs_of_nonneg hn]⟩
  · refine ⟨-O,⟨by simp [hO],by norm_num [Matrix.det_neg,hd]⟩,?_⟩
    simp [ho,abs_of_nonneg hn]
end OMA.S_mo_57550

namespace OMA.S_mo_57550
open Matrix
open scoped RealInnerProductSpace

private lemma pairing_eq {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    (∑ t, ∑ j, y t * M t j * x j) = inner ℝ y (M.toEuclideanLin.toContinuousLinearMap x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ t, ∑ j, y t * M t j * x j) = ∑ t, ((M *ᵥ x.ofLp) t) * star (y t)
  simp only [Matrix.mulVec, dotProduct, star_trivial, Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => by ring

lemma norm_bound_scaled {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    |∑ t, ∑ j, y t * M t j * x j| ≤ (‖M.toEuclideanLin.toContinuousLinearMap‖*‖x‖)*‖y‖ := by
  let L := M.toEuclideanLin.toContinuousLinearMap
  rw [pairing_eq]
  calc |inner ℝ y (L x)| ≤ ‖y‖*‖L x‖ := abs_real_inner_le_norm _ _
       _ ≤ ‖y‖*(‖L‖*‖x‖) := mul_le_mul_of_nonneg_left (L.le_opNorm x) (norm_nonneg _)
       _ = _ := mul_comm _ _

lemma norm_bound {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m))
    (hx : ‖x‖≤1) (hy : ‖y‖≤1) :
    |∑ t, ∑ j, y t * M t j * x j| ≤ ‖M.toEuclideanLin.toContinuousLinearMap‖ := by
  let L := M.toEuclideanLin.toContinuousLinearMap
  rw [pairing_eq]
  calc |inner ℝ y (L x)| ≤ ‖y‖*‖L x‖ := abs_real_inner_le_norm _ _
       _ ≤ ‖L x‖ := mul_le_of_le_one_left (norm_nonneg _) hy
       _ ≤ ‖L‖*‖x‖ := L.le_opNorm _
       _ ≤ ‖L‖ := mul_le_of_le_one_right (norm_nonneg _) hx

lemma norm_witness {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    ∃ x : EuclideanSpace ℝ (Fin n), ∃ y : EuclideanSpace ℝ (Fin m),
      ‖x‖≤1 ∧ ‖y‖≤1 ∧ |∑ t, ∑ j, y t * M t j * x j| = ‖M.toEuclideanLin.toContinuousLinearMap‖ := by
  let L := M.toEuclideanLin.toContinuousLinearMap
  obtain ⟨x,hx,hmax⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr (by norm_num)) L.continuous.norm.continuousOn
  have hxn : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hx
  have hval : ‖L x‖=‖L‖ := le_antisymm ((L.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg _) hxn))
    (ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) (fun z hz => hmax (by simp [Metric.mem_closedBall,hz])))
  refine ⟨x, ‖L x‖⁻¹ • L x, hxn, ?_, ?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    by_cases he : ‖L x‖ = 0 <;> simp [he]
  · rw [pairing_eq]
    change |inner ℝ (‖L x‖⁻¹ • L x) (L x)|=‖L‖
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, ←hval]
    by_cases he : ‖L x‖=0
    · simp [he]
    · rw [sq,←mul_assoc,inv_mul_cancel₀ he,one_mul,abs_of_nonneg (norm_nonneg _)]

end OMA.S_mo_57550

namespace OMA.S_mo_57550
theorem exists_unitNet (d : ℕ) (δ : ℝ) (hδ : 0 < δ) : ∃ X : Finset (Vec d), unitNet δ X := by
  classical
  let B := Metric.closedBall (0 : Vec d) 1
  have compact : IsCompact B := isCompact_closedBall _ _
  obtain ⟨T, hTB, hfin, hcov⟩ :=
    Metric.finite_approx_of_totallyBounded compact.totallyBounded δ hδ
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro x hx
    have := hTB (hfin.mem_toFinset.mp hx)
    simpa [B, Metric.mem_closedBall, dist_zero_right] using this
  · intro x hx
    have h : x ∈ B := by simpa [B, Metric.mem_closedBall, dist_zero_right]
    have hc := hcov h
    simp only [Set.mem_iUnion] at hc
    obtain ⟨u, hu, hxu⟩ := hc
    have hd : dist x u < δ := hxu
    exact ⟨u, hfin.mem_toFinset.mpr hu, by simpa [dist_eq_norm] using hd.le⟩
end OMA.S_mo_57550

namespace OMA.S_mo_57550
open Matrix
private noncomputable def bil {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (x : Vec n) (y : Vec m) := ∑ t, ∑ j, y t * M t j * x j
theorem net_error {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (δ : ℝ)
    (X : Finset (Vec n)) (Y : Finset (Vec m)) (hX : unitNet δ X) (hY : unitNet δ Y) :
    ∃ u ∈ X, ∃ w ∈ Y, (1-2*δ)*‖M.toEuclideanLin.toContinuousLinearMap‖ ≤
      |∑ t, ∑ j, w t * M t j * u j| := by
  obtain ⟨x,y,hx,hy,he⟩ := norm_witness M
  obtain ⟨u,hu,hdu⟩ := hX.2 x hx
  obtain ⟨w,hw,hdw⟩ := hY.2 y hy
  refine ⟨u,hu,w,hw,?_⟩
  let L := ‖M.toEuclideanLin.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  have decomp : bil M x y = bil M (x-u) y + bil M u (y-w) + bil M u w := by
    simp only [bil, PiLp.sub_apply, ←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => by ring
  have b₁ : |bil M (x-u) y| ≤ L*δ := calc
    _ ≤ L*‖x-u‖*‖y‖ := norm_bound_scaled M _ _
    _ ≤ L*‖x-u‖ := mul_le_of_le_one_right (mul_nonneg hL (norm_nonneg _)) hy
    _ ≤ L*δ := mul_le_mul_of_nonneg_left hdu hL
  have b₂ : |bil M u (y-w)| ≤ L*δ := calc
    _ ≤ L*‖u‖*‖y-w‖ := norm_bound_scaled M _ _
    _ ≤ L*‖y-w‖ := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hL (hX.1 u hu)) (norm_nonneg _)
    _ ≤ L*δ := mul_le_mul_of_nonneg_left hdw hL
  have est : L ≤ (L*δ+L*δ)+|bil M u w| := calc
    L = |bil M x y| := he.symm
    _ = _ := congrArg abs decomp
    _ ≤ |bil M (x-u) y + bil M u (y-w)| + |bil M u w| := abs_add_le _ _
    _ ≤ _ := by linarith [abs_add_le (bil M (x-u) y) (bil M u (y-w))]
  change (1-2*δ)*L ≤ |bil M u w|
  linarith
end OMA.S_mo_57550

open OMA.S_mo_57550
open Matrix

theorem OMA.solution : type_of% @OMA.S_mo_57550.main := by
  refine ⟨exists_unitNet, ?_⟩
  intro m n A v
  obtain ⟨R,hR,hmax⟩ := attained A v
  have dual (x : Vec n) (y : Vec m) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
      nuclear (coefficient A v x y) ≤ objective A v R ∧
      ∃ S, rotation S ∧ |(Sᵀ*coefficient A v x y).trace|=nuclear (coefficient A v x y) ∧
        nuclear (coefficient A v x y) ≤ objective A v S := by
    obtain ⟨S,hS,he⟩ := (procrustes (coefficient A v x y)).2
    have hl : nuclear (coefficient A v x y) ≤ objective A v S := by
      rw [←he, trace_pair]
      exact norm_bound _ x y hx hy
    exact ⟨hl.trans (hmax S hS), S, hS, he, hl⟩
  refine ⟨R,hR,hmax,?_,dual,?_⟩
  · obtain ⟨x,y,hx,hy,he⟩ := norm_witness (blockProduct A v R)
    refine ⟨x,y,hx,hy,(dual x y hx hy).1.antisymm ?_⟩
    have bound := (procrustes (coefficient A v x y)).1 R hR
    rw [trace_pair,he] at bound
    exact bound
  · intro δ X Y hX hY
    obtain ⟨u,hu,w,hw,hval⟩ := net_error (blockProduct A v R) δ X Y hX hY
    refine ⟨u,hu,w,hw,hval.trans ?_⟩
    rw [← trace_pair]
    exact (procrustes _).1 R hR
