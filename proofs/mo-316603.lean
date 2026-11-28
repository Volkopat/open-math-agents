import OMAStatements.S_mo_316603
namespace OMA.S_mo_316603
open Matrix
private lemma projection_mul {n : ℕ} (A M : Mat n) (r i j : Fin n) :
    (projection A r*M) i j = M i j - A i r*(A.col r ⬝ᵥ M.col j) := by
  rw [projection, Matrix.sub_mul, Matrix.one_mul, vecMulVec_mul]
  rfl

private lemma idem {n : ℕ} (A : Mat n) (h : ∀ i, A.col i ⬝ᵥ A.col i=1) (j : Fin n) :
    projection A j * projection A j = projection A j := by
  have hh := vecMulVec_mul_vecMulVec (A.col j) (A.col j) (A.col j) (A.col j)
  simp only [h,one_smul] at hh
  unfold projection
  noncomm_ring [hh]

private lemma sweep_times {n : ℕ} (A T : Mat n) (hT : A.transpose*T=lowerGram A) :
    sweep A n*T=T-A := by
  have sub (k : ℕ) (hk : k≤n) (i j : Fin n) :
      (sweep A k*T) i j = T i j - (if j.val<k then A i j else 0) := by
    induction k generalizing i j with
    | zero => simp [sweep]
    | succ k ih =>
      let r : Fin n := ⟨k,by omega⟩
      have he : (sweep A (k+1))*T = projection A r*(sweep A k*T) := by
        simp [sweep,show k<n by omega,r,Matrix.mul_assoc]
      have hcol : (sweep A k*T).col j =
          T.col j - (if j.val<k then A.col j else 0) := by
        funext l
        by_cases h : j.val<k <;> simpa [h] using ih (by omega) l j
      have hG : A.col r ⬝ᵥ T.col j=lowerGram A r j := congrFun (congrFun hT r) j
      have hdot : A.col r ⬝ᵥ (sweep A k*T).col j = if r=j then 1 else 0 := by
        rw [hcol,dotProduct_sub,hG]
        by_cases hj : j.val<k
        · have he : j<r := hj
          have hn : r≠j := he.ne'
          simp [hj, lowerGram,he,hn]
        · have he : ¬j<r := hj
          simp [hj,lowerGram,he]
      rw [he,projection_mul,hdot,ih (by omega)]
      by_cases h : r=j
      · subst j;simp [r]
      · have hne : j.val≠k := fun he => h (Fin.ext he.symm)
        have he : j.val<k+1 ↔ j.val<k := by omega
        simp [h,he]
  ext i j
  simpa [j.isLt] using sub n le_rfl i j

private lemma gram_sum {n : ℕ} (A : Mat n) (hu : ∀ i, A.col i ⬝ᵥ A.col i=1) :
    lowerGram A + (lowerGram A).transpose = 1+A.transpose*A := by
  ext i j
  change (if j < i then _ else if i=j then 1 else 0) + (if i < j then _ else if j=i then 1 else 0) =
    (1:Mat n) i j + A.col i ⬝ᵥ A.col j
  rcases lt_trichotomy i j with h|rfl|h
  · simp [h,not_lt_of_ge h.le,h.ne,dotProduct_comm (A.col j) (A.col i)]
  · simp [hu]
  · simp [h,not_lt_of_ge h.le,h.ne,h.ne']

private lemma energy_matrix {n : ℕ} (A T : Mat n) (hT : A.transpose*T=lowerGram A)
    (hu : ∀ i, A.col i ⬝ᵥ A.col i=1) :
    (sweep A n*T).transpose*(sweep A n*T) = T.transpose*T-1 := by
  rw [sweep_times A T hT,transpose_sub,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,hT]
  have hh : T.transpose*A = (lowerGram A).transpose := by rw [←hT,transpose_mul,transpose_transpose]
  rw [hh]
  have hg : A.transpose*A=lowerGram A+(lowerGram A).transpose-1 := by rw [gram_sum A hu];abel
  rw [hg];abel
private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
private lemma attain {n : ℕ} [NeZero n] (f : E n →L[ℝ] E n) :
    ∃ x : E n, ‖x‖=1 ∧ ‖f x‖=‖f‖ := by
  obtain ⟨x,hx,hm⟩ := (isCompact_sphere (0:E n) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) f.continuous.norm.continuousOn
  have h1 : ‖x‖=1 := by simpa using hx
  refine ⟨x,h1,le_antisymm (by simpa [h1] using f.le_opNorm x) ?_⟩
  exact ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun y hy => hm (by simpa using hy)

private lemma norms_of_energy {n : ℕ} [NeZero n] (q t : E n →L[ℝ] E n)
    (h : ∀ x, ‖q (t x)‖^2 = ‖t x‖^2 - ‖x‖^2) :
    ‖q‖^2 = 1 - ‖t‖⁻¹^2 ∧ 0 < ‖t‖ := by
  have hi : Function.Injective t := by
    change Function.Injective t.toLinearMap
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change t x=0 at hx
    have hh := h x
    simp [hx] at hh
    exact hh
  have hs : Function.Surjective t := (LinearMap.injective_iff_surjective (f := t.toLinearMap)).mp hi
  obtain ⟨x,hx,hx'⟩ := attain t
  obtain ⟨y,hy,hy'⟩ := attain q
  have ht : 0 < ‖t‖ := by
    rw [← hx',norm_pos_iff]
    intro hz
    have := hi (hz.trans (map_zero t).symm)
    simp [this] at hx
  have h1 := h x
  rw [hx,hx',one_pow] at h1
  have h2 := q.le_opNorm (t x)
  rw [hx'] at h2
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  obtain ⟨z,hz⟩ := hs y
  have hy1 := h z
  rw [hz,hy,hy',one_pow] at hy1
  have h4 := t.le_opNorm z
  rw [hz,hy] at h4
  have h5 := pow_le_pow_left₀ zero_le_one h4 2
  have hgt : ‖q‖^2*‖t‖^2 = ‖t‖^2-1 := by
    apply le_antisymm
    · rw [eq_sub_iff_add_eq] at hy1
      nlinarith only [h5,congrArg (fun a : ℝ => a*‖t‖^2) hy1]
    · nlinarith only [h1,h3]
  refine ⟨?_,ht⟩
  field_simp
  linarith

private lemma op_energy {n : ℕ} (Q T : Mat n)
    (h : (Q*T).transpose*(Q*T)=T.transpose*T-1) :
    ∀ x : E n, ‖(toEuclideanCLM (𝕜 := ℝ) Q) (toEuclideanCLM (𝕜 := ℝ) T x)‖^2 =
      ‖toEuclideanCLM (𝕜 := ℝ) T x‖^2 - ‖x‖^2 := by
  intro x
  have hh := congrArg (fun M : Mat n => inner ℝ x (toEuclideanCLM (𝕜 := ℝ) M x)) h
  change inner ℝ x (toEuclideanCLM (𝕜 := ℝ) (star (Q*T)*(Q*T)) x) =
    inner ℝ x (toEuclideanCLM (𝕜 := ℝ) (star T*T-1) x) at hh
  simp only [map_mul,map_star,map_sub,map_one,mul_apply_eq_comp,
    _root_.sub_apply,one_apply_eq_self,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,inner_sub_right,real_inner_self_eq_norm_sq] at hh
  exact hh

end OMA.S_mo_316603

open OMA.S_mo_316603 Matrix in
theorem OMA.solution : type_of% @OMA.S_mo_316603.main := by
  intro n hn A hA hu
  let : NeZero n := ⟨hn.ne'⟩
  let Q := sweep A n
  let T := A.transpose⁻¹*lowerGram A
  have hT : A.transpose*T = lowerGram A := by
    simp [T, ←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (A.isUnit_det_transpose hA)]
  have he := op_energy Q T (energy_matrix A T hT hu)
  have hnrm := norms_of_energy (toEuclideanCLM (𝕜 := ℝ) Q) (toEuclideanCLM (𝕜 := ℝ) T) he
  have hQ : opNorm (Q.transpose*Q) = (opNorm Q)^2 := by
    change ‖toEuclideanCLM (𝕜 := ℝ) (star Q*Q)‖=‖toEuclideanCLM (𝕜 := ℝ) Q‖^2
    rw [map_mul,map_star,pow_two]
    exact ContinuousLinearMap.norm_adjoint_comp_self _
  refine ⟨idem A hu,hQ.trans hnrm.1,?_⟩
  change opNorm (Q.transpose*Q)<1
  rw [hQ,show (opNorm Q)^2=1-(opNorm T)⁻¹^2 from hnrm.1]
  have hp : 0<opNorm T := hnrm.2
  exact sub_lt_self _ (by positivity)
