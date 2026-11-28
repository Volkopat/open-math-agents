import OMAStatements.S_mo_442655

/-! Proof of jacaboul’s MathOverflow question 442655. Credit: @connoranderson. -/

namespace OMA.S_mo_442655
open Matrix Complex Finset

private lemma euclid_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ euclid x := norm_nonneg _

private lemma sq_dot {n : ℕ} (x : Fin n → ℂ) :
    euclid x ^ 2 = (star x ⬝ᵥ x).re := by
  rw [euclid, EuclideanSpace.norm_sq_eq, dotProduct, Complex.re_sum]
  apply sum_congr rfl
  intro i _
  change ‖x i‖ ^ 2 = (star (x i) * x i).re
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]

private lemma isometry {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (x : Fin n → ℂ) :
    euclid ((U : Mat n) *ᵥ x) = euclid x := by
  apply (sq_eq_sq₀ (euclid_nonneg _) (euclid_nonneg _)).mp
  rw [sq_dot,sq_dot,star_mulVec,dotProduct_mulVec,vecMul_vecMul]
  have h : (U : Mat n)ᴴ * (U : Mat n) = 1 := U.2.1
  rw [h,vecMul_one]

private lemma conj_iso {n : ℕ} (x : Fin n → ℂ) : euclid (star x) = euclid x := by
  apply (sq_eq_sq₀ (euclid_nonneg _) (euclid_nonneg _)).mp
  rw [sq_dot,sq_dot,star_star,dotProduct_comm]

private lemma sub_sq {n : ℕ} (x y : Fin n → ℂ) :
    euclid (x-y)^2 = euclid x^2 + euclid y^2 - 2*(star x ⬝ᵥ y).re := by
  simp only [sq_dot, star_sub, sub_dotProduct, dotProduct_sub, Complex.sub_re]
  have hh := congrArg Complex.re (star_dotProduct y x)
  simp only [Complex.star_def, Complex.conj_re] at hh
  linarith

private lemma mul_I_iso {n : ℕ} (x : Fin n → ℂ) : euclid (I • x) = euclid x := by
  change ‖I • (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ = _
  simp [norm_smul,euclid]

private lemma reduced {n : ℕ} {r : ℝ} (h : r ∈ radii n) :
    ∃ W : Matrix.unitaryGroup (Fin n) ℂ, ∀ x : Fin n → ℂ,
      euclid (x-(W : Mat n) *ᵥ star x) ≤ r*euclid x := by
  obtain ⟨_,U,V,h⟩ := h
  refine ⟨U⁻¹*V,fun x => ?_⟩
  rw [← isometry U (x-_),mulVec_sub,mulVec_mulVec]
  have he : (U : Mat n) * ((U⁻¹*V : Matrix.unitaryGroup (Fin n) ℂ) : Mat n) = (V : Mat n) := by
    change ((U*(U⁻¹*V) : Matrix.unitaryGroup (Fin n) ℂ) : Mat n) = _
    simp
  rw [he]
  exact h x

private lemma sqrt_lower {n : ℕ} (hn : 0<n) {r : ℝ} (hr : r ∈ radii n) : √2 ≤ r := by
  obtain ⟨W,h⟩ := reduced hr
  let i : Fin n := ⟨0,hn⟩
  let x : Fin n → ℂ := Pi.single i 1
  let y := (W : Mat n) *ᵥ star x
  have hx : euclid x = 1 := by
    rw [euclid, EuclideanSpace.norm_eq]
    simp [x,Pi.single_apply,apply_ite]
  have hy : euclid y = 1 := (isometry W _).trans ((conj_iso x).trans hx)
  have h₁ := h x
  change euclid (x-y) ≤ _ at h₁
  rw [hx,mul_one] at h₁
  have h₂ := h (I • x)
  have he : (I • x) - (W : Mat n) *ᵥ star (I • x) = I • (x - -y) := by
    simp [y,star_smul,mulVec_neg,mulVec_smul]
  rw [he,mul_I_iso,mul_I_iso,hx,mul_one] at h₂
  have h₃ := sq_le_sq' ((neg_nonpos.mpr hr.1).trans (euclid_nonneg _)) h₁
  have h₄ := sq_le_sq' ((neg_nonpos.mpr hr.1).trans (euclid_nonneg _)) h₂
  have hy' : euclid (-y) = euclid y := by
    change ‖-(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n))‖ = _
    exact norm_neg _
  simp only [sub_sq,hx,hy',hy,dotProduct_neg,Complex.neg_re] at h₃ h₄
  nlinarith [hr.1,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

private lemma odd_antivector {n : ℕ} (ho : Odd n) (W : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ z : Fin n → ℂ, z ≠ 0 ∧ (W : Mat n) *ᵥ star z = -z := by
  let M : Mat n := (W : Mat n) - (W : Mat n)ᵀ
  have ht : Mᵀ = -M := by simp [M, neg_sub]
  have hd := M.det_transpose
  rw [ht, det_neg,Fintype.card_fin,ho.neg_one_pow,neg_one_mul] at hd
  have hz : M.det=0 := by linear_combination -hd/2
  obtain ⟨v,hv,he⟩ := (Matrix.exists_mulVec_eq_zero_iff.mpr hz)
  change ((W : Mat n)-(W : Mat n)ᵀ) *ᵥ v = 0 at he
  rw [sub_mulVec,sub_eq_zero] at he
  let T (x : Fin n → ℂ) := (W : Mat n) *ᵥ star x
  let z := star v
  have hzz : z ≠ 0 := by simpa [z] using hv
  have ht2 : T (T z) = z := by
    simp only [T,z,star_star]
    rw [he,mulVec_transpose,star_vecMul,mulVec_mulVec]
    have hu : (W : Mat n)*(W : Mat n)ᴴ=1 := W.2.2
    rw [hu,one_mulVec]
  by_cases h : z=T z
  · refine ⟨I • z, smul_ne_zero I_ne_zero hzz, ?_⟩
    change T (I • z) = _
    have hh : T (I • z) = -(I • T z) := by simp [T,star_smul,mulVec_neg,mulVec_smul]
    rw [hh,←h]
  · refine ⟨z-T z, sub_ne_zero.mpr h,?_⟩
    change T (z-T z) = _
    have hh (a b) : T (a-b)=T a-T b := by simp [T,star_sub,mulVec_sub]
    rw [hh,ht2,neg_sub]

private lemma odd_lower {n : ℕ} (ho : Odd n) {r : ℝ} (hr : r ∈ radii n) : 2 ≤ r := by
  obtain ⟨W,hW⟩ := reduced hr
  obtain ⟨z,hz,hT⟩ := odd_antivector ho W
  have h := hW z
  rw [hT,sub_neg_eq_add,←two_smul ℂ z] at h
  have he : euclid ((2:ℂ) • z) = 2 * euclid z := by
    change ‖(2:ℂ) • (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin n))‖ = _
    simp [norm_smul,euclid]
  rw [he] at h
  apply le_of_not_gt
  intro h'
  have hz' : 0 < euclid z := norm_pos_iff.mpr (by simpa using hz)
  exact (not_lt_of_ge h) (mul_lt_mul_of_pos_right h' hz')

private lemma two_mem (n : ℕ) : 2 ∈ radii n := by
  refine ⟨by norm_num,1,1,fun x => ?_⟩
  simp only [Matrix.UnitaryGroup.one_val,one_mulVec]
  have h : euclid (x-star x) ≤ euclid x + euclid (star x) := norm_sub_le _ _
  rw [conj_iso] at h
  linarith

private lemma even_skew {n : ℕ} (he : Even n) : ∃ W : Matrix.unitaryGroup (Fin n) ℂ,
    (W : Mat n)ᵀ = -(W : Mat n) := by
  obtain ⟨m,hm⟩ := he
  let e : Fin n ≃ Fin m ⊕ Fin m := Fintype.equivOfCardEq (by simp [hm])
  let J' := Matrix.J (Fin m) ℂ
  have hj : J'ᴴ = -J' := by
    change (J'.map (starRingEnd ℂ))ᵀ = _
    simp [J']
  let W := J'.submatrix e e
  have hw : W ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change Wᴴ * W = 1
    simp only [W,conjTranspose_submatrix,submatrix_mul_equiv,hj,neg_mul,J',J_squared,neg_neg,submatrix_one_equiv]
  refine ⟨⟨W,hw⟩,?_⟩
  change (J'.submatrix e e)ᵀ = _
  rw [transpose_submatrix,show J'ᵀ = -J' from Matrix.J_transpose ..,submatrix_neg]
  rfl

private lemma sqrt_mem {n : ℕ} (he : Even n) : √2 ∈ radii n := by
  obtain ⟨W,hW⟩ := even_skew he
  refine ⟨Real.sqrt_nonneg _,1,W, fun x => ?_⟩
  simp only [Matrix.UnitaryGroup.one_val,one_mulVec]
  have h := dotProduct_transpose_mulVec (W : Mat n) (star x) (star x)
  rw [hW,neg_mulVec,dotProduct_neg] at h
  have hz : star x ⬝ᵥ ((W : Mat n) *ᵥ star x) = 0 := by linear_combination -h/2
  have hn := sub_sq x ((W : Mat n) *ᵥ star x)
  rw [hz,isometry,conj_iso] at hn
  apply (sq_le_sq₀ (euclid_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (euclid_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  simp at hn
  linarith

end OMA.S_mo_442655

theorem OMA.solution : type_of% @OMA.S_mo_442655.main := by
  intro n hn
  by_cases he : Even n
  · rw [if_pos he]
    exact ⟨OMA.S_mo_442655.sqrt_mem he, fun _ h => OMA.S_mo_442655.sqrt_lower hn h⟩
  · rw [if_neg he]
    exact ⟨OMA.S_mo_442655.two_mem n, fun _ h => OMA.S_mo_442655.odd_lower (Nat.not_even_iff_odd.mp he) h⟩
