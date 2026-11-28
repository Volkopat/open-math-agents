import OMAStatements.S_mo_163012

namespace OMA.S_mo_163012
open Matrix Finset
private noncomputable def assemble {n : ℕ} (Q : CMat n) (z : Fin n → ℂ) : CMat n :=
  Q*diagonal z*Qᴴ

private theorem assemble_mul {n : ℕ} (Q : CMat n) (hQ : Qᴴ*Q=1) (x y : Fin n → ℂ) :
  assemble Q x * assemble Q y = assemble Q (fun k => x k*y k) := by
  unfold assemble
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Qᴴ Q,hQ,one_mul,← Matrix.mul_assoc (diagonal x),diagonal_mul_diagonal]

private theorem assemble_one {n : ℕ} (Q : CMat n) (hQ : Q*Qᴴ=1) :
    assemble Q (fun _ => 1) = 1 := by simpa [assemble] using hQ

private theorem assemble_sub {n : ℕ} (Q : CMat n) (x y : Fin n → ℂ) :
    assemble Q (fun k => x k-y k)=assemble Q x-assemble Q y := by
  simp [assemble,← diagonal_sub,Matrix.mul_sub,Matrix.sub_mul]

private theorem assemble_smul {n : ℕ} (Q : CMat n) (z : ℂ) (x : Fin n → ℂ) :
    assemble Q (fun k => z*x k)= z • assemble Q x := by
  have h : diagonal (fun k => z*x k) = z • diagonal x := by ext i j; by_cases e : i=j <;> simp [diagonal,e]
  simp [assemble,h]

private theorem shift_sub_ne (δ t : ℝ) (hd : 0<δ) : shift δ-(t:ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [shift] at this
  linarith

private theorem resolvent_diag {n : ℕ} (Q : CMat n) (hq : Qᴴ*Q=1) (qq : Q*Qᴴ=1)
    (d : Fin n → ℝ) (δ : ℝ) (hd : 0<δ) :
    IsUnit (shift δ • 1-assemble Q (fun k => (d k:ℂ))) ∧
    resolvent (assemble Q (fun k => (d k:ℂ))) δ = assemble Q (fun k => (shift δ-(d k:ℂ))⁻¹) := by
  have hs : shift δ • (1 : CMat n)-assemble Q (fun k => (d k:ℂ)) =
      assemble Q (fun k => shift δ-(d k:ℂ)) := by
    rw [assemble_sub]
    have := assemble_smul Q (shift δ) (fun _ => 1)
    simpa [assemble_one Q qq] using congrArg (fun M => M-assemble Q (fun k => (d k:ℂ))) this.symm
  have he : (shift δ • (1 : CMat n)-assemble Q (fun k => (d k:ℂ))) *
      assemble Q (fun k => (shift δ-(d k:ℂ))⁻¹) = 1 := by
    rw [hs,assemble_mul Q hq]
    simpa [mul_inv_cancel₀ (shift_sub_ne δ _ hd)] using assemble_one Q qq
  refine ⟨?_,Matrix.inv_eq_right_inv he⟩
  apply (Matrix.isUnit_iff_isUnit_det _).2
  have h := congrArg Matrix.det he
  rw [det_mul,det_one] at h
  exact isUnit_iff_ne_zero.mpr (fun hz => by simp [hz] at h)

private theorem unit_rows {n : ℕ} (U : CMat n) (h : U*Uᴴ=1) (i : Fin n) :
    rowSize U i ≤ Real.sqrt n := by
  have he := congrArg (fun M : CMat n => (M i i).re) h
  have hs : (∑ j, ‖U i j‖^2)=1 := by
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.mul_conj,Complex.sq_norm] using he
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt univ (fun _ : Fin n => (1:ℝ)) (fun j => ‖U i j‖)
  simpa [rowSize,hs] using hcs

private theorem phase_norm (δ t : ℝ) (hd : 0<δ) : ‖2*shift δ*(shift δ-(t:ℂ))⁻¹-1‖=1 := by
  have hh : 2*shift δ*(shift δ-(t:ℂ))⁻¹-1 = (shift δ+t)/(shift δ-t) := by
    field_simp [shift_sub_ne δ t hd]; ring
  rw [hh,norm_div,div_eq_one_iff_eq (norm_ne_zero_iff.mpr (shift_sub_ne δ t hd))]
  rw [Complex.norm_def,Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply,shift]

private theorem upper {n : ℕ} (A : CMat n) (δ : ℝ) (ha : A.IsHermitian) (hd : 0<δ) :
    IsUnit (shift δ • 1-A) ∧ ∀ i, rowSize (resolvent A δ) i ≤ (1+Real.sqrt n)/(2*δ) := by
  let Q : CMat n := ha.eigenvectorUnitary
  have hq : Qᴴ*Q=1 := Unitary.coe_star_mul_self ha.eigenvectorUnitary
  have qq : Q*Qᴴ=1 := Unitary.coe_mul_star_self ha.eigenvectorUnitary
  have hA : A=assemble Q (fun k => (ha.eigenvalues k:ℂ)) := ha.spectral_theorem
  obtain ⟨hu,hr⟩ := resolvent_diag Q hq qq ha.eigenvalues δ hd
  rw [← hA] at hu hr
  refine ⟨hu,fun i => ?_⟩
  let v (k : Fin n) := 2*shift δ*(shift δ-(ha.eigenvalues k:ℂ))⁻¹-1
  let U := assemble Q v
  have hunit : U*Uᴴ=1 := by
    have hh : Uᴴ=assemble Q (fun k => star (v k)) := by
      simp [U,assemble,conjTranspose_mul,diagonal_conjTranspose, Matrix.mul_assoc]
      rfl
    rw [hh,show U=assemble Q v from rfl,assemble_mul Q hq]
    have hv (k : Fin n) : v k*star (v k)=1 := by
      rw [Complex.star_def,Complex.mul_conj,← Complex.sq_norm,show ‖v k‖=1 from phase_norm _ _ hd]
      norm_num
    rw [show (fun k => v k*star (v k)) = (fun _ => 1) from funext hv,assemble_one Q qq]
  have hmat : (2*shift δ) • resolvent A δ=U+1 := by
    have hU : U=(2*shift δ) • resolvent A δ-1 := by
      dsimp [U,v]
      rw [assemble_sub,assemble_one Q qq,assemble_smul,hr]
    rw [hU]; abel
  have hnorm : ‖shift δ‖=δ := by simp [shift,Real.norm_eq_abs,abs_of_pos hd]
  have size : (2*δ)*rowSize (resolvent A δ) i ≤ rowSize U i+1 := by
    calc (2*δ)*rowSize (resolvent A δ) i = rowSize ((2*shift δ) • resolvent A δ) i := by
          simp [rowSize,Matrix.smul_apply,hnorm,Finset.mul_sum]
         _ = rowSize (U+1) i := by rw [hmat]
         _ ≤ ∑ j, (‖U i j‖+‖(1:CMat n) i j‖) := Finset.sum_le_sum (fun j _ => norm_add_le _ _)
         _ = rowSize U i+1 := by simp [rowSize,Finset.sum_add_distrib,Matrix.one_apply,apply_ite (fun z : ℂ => ‖z‖)]
  apply (le_div_iff₀ (by positivity)).2
  linarith [unit_rows U hunit i]

end OMA.S_mo_163012

namespace OMA.S_mo_163012
open Matrix Finset
open scoped InnerProductSpace

lemma extremal_basis (n : ℕ) [NeZero n] : ∃ Q : Matrix (Fin n) (Fin n) ℝ,
    Qᵀ*Q=1 ∧ Q*Qᵀ=1 ∧ (∑ j, |Q 0 0 * Q j 0|)=(1+Real.sqrt n)/2 := by
  classical
  let s := Real.sqrt (n:ℝ)
  have hs : 0<s := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
  have hn : (n:ℝ)=s^2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
  let u : Fin n → ℝ := fun j => (if j=0 then 1 else 0)+1/s
  have hsum : ∑ j, u j = 1+s := by
    simp only [u,sum_add_distrib,sum_ite_eq',mem_univ,if_true,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    rw [hn]
    field_simp
  have hsum2 : ∑ j, (u j)^2 = 2+2/s := by
    have hh (j : Fin n) : u j ^ 2 = (if j=0 then 1+2/s else 0) + (1/s)^2 := by
      by_cases h : j=0 <;> simp [u,h]
      ring
    simp only [hh,sum_add_distrib,sum_ite_eq',mem_univ,if_true,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    rw [hn]
    field_simp
    ring
  let c := Real.sqrt (2+2/s)
  have hc : 0<c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c^2=2+2/s := Real.sq_sqrt (by positivity)
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => u j/c)
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hv : ‖v‖=1 := by
    have hh : ‖v‖^2=1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [v,Real.norm_eq_abs,sq_abs, div_pow, ← sum_div,hsum2,
        hc2]
      exact div_self (by positivity)
    nlinarith [norm_nonneg v]
  let T := Submodule.reflection (ℝ ∙ (b 0-v))ᗮ
  have hT : T (b 0) = v := Submodule.reflection_sub (by rw [hv,b.orthonormal.norm_eq_one])
  let Q := T.toMatrix b.toBasis b.toBasis
  have hu := T.toMatrix_mem_unitaryGroup b b
  have hQ (j : Fin n) : Q j 0 = u j/c := by
    simp only [Q, LinearMap.toMatrix_apply]
    change b.toBasis.repr (T (b 0)) j = _
    rw [hT]
    rfl
  refine ⟨Q, ?_, ?_, ?_⟩
  · simpa [Q, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using hu
  · simpa [Q, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using hu
  · have hnon (j : Fin n) : 0≤u j := by dsimp [u]; split <;> positivity
    simp only [hQ,abs_of_nonneg (mul_nonneg (div_nonneg (hnon 0) hc.le) (div_nonneg (hnon _) hc.le))]
    rw [← mul_sum, ← sum_div, hsum]
    simp only [u,if_true]
    change (1+1/s)/c*((1+s)/c)=(1+s)/2
    field_simp
    nlinarith [show c^2*s=2*s+2 by rw [hc2]; field_simp]
end OMA.S_mo_163012

namespace OMA.S_mo_163012
open Matrix Filter Topology Finset

private theorem cmul {n : ℕ} (A B : RMat n) : complexify (A*B) = complexify A*complexify B :=
  Matrix.map_mul (f := Complex.ofRealHom)

private theorem cstar {n : ℕ} (A : RMat n) : complexify Aᵀ=(complexify A)ᴴ := by
  ext i j
  simp [complexify,Matrix.conjTranspose_apply]

private theorem cone {n : ℕ} : complexify (1:RMat n)=1 := by
  ext i j; by_cases h : i=j <;> simp [complexify,Matrix.one_apply,h]

private theorem assemble_apply {n : ℕ} (Q : CMat n) (z : Fin n → ℂ) (i j : Fin n) :
    assemble Q z i j = ∑ k, Q i k*z k*star (Q j k) := by
  unfold assemble
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

private theorem scaled_limit (t : ℝ) :
    Tendsto (fun δ : ℝ => shift δ*(shift δ-(t:ℂ))⁻¹) (𝓝[>] 0)
      (𝓝 (if t=0 then (1:ℂ) else 0)) := by
  by_cases h : t=0
  · subst t
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hz := shift_sub_ne δ 0 hδ
    simp_all
  · have hc : Continuous shift := by unfold shift; fun_prop
    have h0 : shift 0-(t:ℂ)≠0 := by simp [shift,h]
    have ht := hc.continuousAt.mul ((hc.continuousAt.sub continuousAt_const).inv₀ h0)
    have hh : Tendsto (fun δ : ℝ => shift δ*(shift δ-(t:ℂ))⁻¹) (𝓝[>] 0)
        (𝓝 (shift 0*(shift 0-(t:ℂ))⁻¹)) := ht.tendsto.mono_left nhdsWithin_le_nhds
    simpa [shift,h] using hh

private theorem sharp_limit (n : ℕ) [NeZero n] :
    ∃ (Q : RMat n) (d : Fin n → ℝ), Qᵀ*Q=1 ∧ Q*Qᵀ=1 ∧ Function.Injective d ∧
      (∀ i, d i ∈ Set.Icc (0:ℝ) 1) ∧ Tendsto (fun δ : ℝ =>
        δ*rowSize (resolvent (complexify (Q*diagonal d*Qᵀ)) δ) 0) (𝓝[>] 0)
          (𝓝 ((1+Real.sqrt n)/2)) := by
  obtain ⟨Q,hq,qq,hsharp⟩ := extremal_basis n
  let d (i : Fin n) : ℝ := (i.val:ℝ)/n
  have hn : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have dinj : Function.Injective d := by
    intro i j hij
    apply Fin.ext
    exact_mod_cast (div_left_inj' hn.ne').mp hij
  have d0 : d 0=0 := by simp [d]
  have dz (k : Fin n) : d k=0 ↔ k=0 := by rw [← d0]; exact dinj.eq_iff
  refine ⟨Q,d,hq,qq,dinj,fun i => ⟨div_nonneg (by positivity) hn.le,
    (div_le_one hn).2 (by exact_mod_cast i.isLt.le)⟩,?_⟩
  let C := complexify Q
  have cq : Cᴴ*C=1 := by rw [← cstar,← cmul,hq,cone]
  have qc : C*Cᴴ=1 := by rw [← cstar,← cmul,qq,cone]
  have hA : complexify (Q*diagonal d*Qᵀ)=assemble C (fun k => (d k:ℂ)) := by
    rw [cmul,cmul,cstar]
    have dd : complexify (diagonal d)=diagonal (fun k => (d k:ℂ)) := by
      ext i j; by_cases h : i=j <;> simp [complexify,diagonal,h]
    rw [dd]; rfl
  let z (δ : ℝ) (k : Fin n) := shift δ*(shift δ-(d k:ℂ))⁻¹
  have hent (j : Fin n) : Tendsto (fun δ : ℝ => assemble C (z δ) 0 j) (𝓝[>] 0)
      (𝓝 ((Q 0 0*Q j 0 : ℝ):ℂ)) := by
    have h := tendsto_finsetSum (a := fun k => C 0 k*(if d k=0 then (1:ℂ) else 0)*star (C j k))
      (f := fun k δ => C 0 k*z δ k*star (C j k)) univ (fun k _ =>
        (tendsto_const_nhds.mul (scaled_limit (d k))).mul tendsto_const_nhds)
    simpa [assemble_apply, dz, mul_ite, ite_mul, C, complexify] using h
  have hrow := tendsto_finsetSum (f := fun j δ => ‖assemble C (z δ) 0 j‖) univ
    (fun j _ => (hent j).norm)
  have hs : Tendsto (fun δ => rowSize (assemble C (z δ)) 0) (𝓝[>] 0) (𝓝 ((1+Real.sqrt n)/2)) := by
    rw [← hsharp]
    simpa [rowSize,Real.norm_eq_abs] using hrow
  apply (tendsto_congr' ?_).2 hs
  filter_upwards [self_mem_nhdsWithin] with δ hd
  have hd' : 0 < δ := hd
  rw [hA,(resolvent_diag C cq qc d δ hd').2]
  have he : assemble C (z δ) = shift δ • assemble C (fun k => (shift δ-(d k:ℂ))⁻¹) :=
    assemble_smul _ _ _
  rw [he]
  simp [rowSize,shift,Real.norm_eq_abs,abs_of_pos hd',Finset.mul_sum]

end OMA.S_mo_163012

open OMA.S_mo_163012
theorem OMA.solution : type_of% @OMA.S_mo_163012.main := by
  exact ⟨fun _ _ _ => upper _ _,sharp_limit⟩
