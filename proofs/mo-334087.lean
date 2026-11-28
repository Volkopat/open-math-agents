import OMAStatements.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset
theorem shiftedHerm {n : ℕ} {A : Mat n} (h : A.PosSemidef) (k : ℕ) : (shifted A k).IsHermitian :=
  h.1.sub ((isHermitian_diagonal_iff.mpr fun _ => IsSelfAdjoint.all _).smul (IsSelfAdjoint.all (k:ℝ)))
end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset
private abbrev Vec (n : ℕ) := Fin n → ℝ

lemma projection_bound {n : ℕ} (P : Mat n) (hp : P.IsHermitian) (he : P*P=P) :
    (((n:ℝ)+1-P.trace) • diagPart P - P).PosSemidef := by
  have hsym (i j : Fin n) : P j i=P i j := hp.apply i j
  have hrow (i : Fin n) : (∑ j,(P i j)^2)=P i i := by
    have hh := congrArg (fun M : Mat n => M i i) he
    simpa only [Matrix.mul_apply,fun j => hsym i j,pow_two] using hh
  have hd0 (i : Fin n) : 0≤P i i := (sum_nonneg fun j _ => sq_nonneg (P i j)).trans_eq (hrow i)
  have hd1 (i : Fin n) : P i i≤1 := by
    have h := single_le_sum (s:=univ) (f:=fun j => (P i j)^2)
      (fun j _ => sq_nonneg (P i j)) (mem_univ i)
    rw [hrow] at h
    nlinarith
  have htr : (∑ i, (1-P i i))=(n:ℝ)-P.trace := by simp [sum_sub_distrib,Matrix.trace]
  have hk : 0≤(n:ℝ)+1-P.trace := by
    linarith [htr,sum_nonneg (s:=univ) (fun i _ => sub_nonneg.mpr (hd1 i))]
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨((isHermitian_diagonal_iff.mpr fun _ => IsSelfAdjoint.all _).smul (IsSelfAdjoint.all _)).sub hp,?_⟩
  intro x
  let y := P *ᵥ x
  let S := ∑ i,(y i)^2
  let W := ∑ i,P i i*(x i)^2
  have hfix : P*ᵥy=y := by change P*ᵥ(P*ᵥx)=P*ᵥx; rw [mulVec_mulVec,he]
  have hS : 0≤S := sum_nonneg fun _ _ => sq_nonneg _
  have hW : 0≤W := sum_nonneg fun i _ => mul_nonneg (hd0 i) (sq_nonneg _)
  have hxy : x ⬝ᵥ y = S := by
    rw [← hfix,Matrix.dotProduct_mulVec]
    have ht : P.transpose=P := hp
    have hy : x ᵥ* P=y := by rw [← ht,vecMul_transpose]
    rw [hy]
    simp [S,dotProduct,pow_two]
  have hcoord (i : Fin n) : (y i)^2 ≤ P i i*S := by
    have hy : (∑ j,P i j*y j)=y i := congrFun hfix i
    simpa only [hy,hrow,S] using sum_mul_sq_le_sq_mul_sq univ (P i) y
  let g := fun i => (y i)^2 + (1-P i i)*S
  have hg (i : Fin n) : 0≤g i := add_nonneg (sq_nonneg _) (mul_nonneg (by linarith [hd1 i]) hS)
  have ht (i : Fin n) : (x i*y i)^2 ≤ (P i i*(x i)^2)*g i := by
    have h := mul_nonneg (sub_nonneg.mpr (hd1 i)) (sub_nonneg.mpr (hcoord i))
    have hc : (y i)^2 ≤ P i i*g i := by dsimp [g]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (x i))]
  have hgs : (∑ i,g i) = ((n:ℝ)+1-P.trace)*S := by
    simp only [g,sum_add_distrib,← sum_mul,htr]
    change S+_ = _
    ring
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (fun i _ => mul_nonneg (hd0 i) (sq_nonneg (x i))) (fun i _ => hg i) (fun i _ => ht i)
  change (x ⬝ᵥ y)^2 ≤ W*∑ i,g i at hcs
  rw [hxy,hgs] at hcs
  have hfinal : S≤((n:ℝ)+1-P.trace)*W := by
    rcases hS.eq_or_lt with h|h
    · rw [← h]; exact mul_nonneg hk hW
    · apply (mul_le_mul_iff_left₀ h).mp
      nlinarith [hcs]
  have hw : x ⬝ᵥ (diagPart P *ᵥ x) = W := by
    simp only [diagPart,dotProduct,mulVec_diagonal,W]
    exact sum_congr rfl fun i _ => by ring
  rw [show star x=x by rfl,sub_mulVec,dotProduct_sub,smul_mulVec,dotProduct_smul,hw]
  change 0 ≤ _*W-x ⬝ᵥ y
  linarith
end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset Unitary

private lemma psd_trace_product {n : ℕ} {A B : Mat n} (ha : A.PosSemidef) (hb : B.PosSemidef) :
    0 ≤ (B*A).trace := by
  let U : unitary (Mat n) := ha.1.eigenvectorUnitary
  let L := diagonal ha.1.eigenvalues
  have hs : A = (U : Mat n) * L * star (U : Mat n) := by
    simpa [U,L,conjStarAlgAut_apply] using ha.1.spectral_theorem
  have hps : ((star (U : Mat n))*B*(U : Mat n)).PosSemidef := hb.conjTranspose_mul_mul_same _
  rw [hs,← Matrix.mul_assoc,trace_mul_comm,← Matrix.mul_assoc,← Matrix.mul_assoc]
  change 0 ≤ ∑ i, ((star (U : Mat n)*B*(U : Mat n))*L) i i
  apply Finset.sum_nonneg
  intro i _
  rw [show L = diagonal ha.1.eigenvalues from rfl,Matrix.mul_diagonal]
  exact mul_nonneg hps.diag_nonneg (ha.eigenvalues_nonneg i)

private lemma trace_shift {n : ℕ} (A P : Mat n) (k : ℕ) (ha : A.PosSemidef)
    (hp : ((k:ℝ) • diagPart P - P).PosSemidef) : (P*shifted A k).trace ≤ 0 := by
  have h := psd_trace_product ha hp
  have hdiag : (diagPart P * A).trace=(P*diagPart A).trace := by
    simp [diagPart,Matrix.trace,Matrix.diag,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rw [sub_mul,Matrix.smul_mul,trace_sub,trace_smul,hdiag] at h
  rw [shifted,mul_sub,Matrix.mul_smul,trace_sub,trace_smul]
  simpa only [smul_eq_mul,sub_nonpos,sub_nonneg] using h

private lemma trace_conj {n : ℕ} (U : unitary (Mat n)) (M : Mat n) :
    (conjStarAlgAut ℝ _ U M).trace = M.trace := by
  rw [conjStarAlgAut_apply,trace_mul_cycle,Unitary.coe_star_mul_self,one_mul]

private lemma eigen_sum {n : ℕ} (A : Mat n) (ha : A.PosSemidef) (k : ℕ) (S : Finset (Fin n))
    (hcard : S.card+k=n+1)
    (bound : ∀ P : Mat n, P.IsHermitian → P*P=P →
        (((n:ℝ)+1-P.trace) • diagPart P - P).PosSemidef) :
    ∑ i ∈ S, (shiftedHerm ha k).eigenvalues i ≤ 0 := by
  let H := shifted A k
  let hs : H.IsHermitian := shiftedHerm ha k
  let U := hs.eigenvectorUnitary
  let F := conjStarAlgAut ℝ _ U
  let e : Fin n → ℝ := fun i => if i ∈ S then 1 else 0
  let E := diagonal e
  let P := F E
  have hE : E.IsHermitian := isHermitian_diagonal_iff.mpr fun _ => IsSelfAdjoint.all _
  have hP : P.IsHermitian := by
    change star (F E)=F E
    rw [← map_star,show star E=E from hE]
  have hEE : E*E=E := by
    change diagonal e * diagonal e = diagonal e
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i∈S <;> simp [e,hi]
  have hPP : P*P=P := by change F E*F E=F E; rw [← map_mul,hEE]
  have htr : P.trace=(S.card:ℝ) := by
    change (conjStarAlgAut ℝ _ U E).trace=_
    rw [trace_conj,show E=diagonal e from rfl,trace_diagonal]
    simp [e]
  have hc : (n:ℝ)+1-P.trace=k := by
    rw [htr]
    have he : (S.card:ℝ)+(k:ℝ)=(n:ℝ)+1 := by exact_mod_cast hcard
    linarith
  have hb := bound P hP hPP
  rw [hc] at hb
  have ht := trace_shift A P k ha hb
  have spec : H = F (diagonal hs.eigenvalues) := by simpa [F,U] using hs.spectral_theorem
  change (P*H).trace ≤ 0 at ht
  rw [spec,show P=F E from rfl,← map_mul,trace_conj] at ht
  change (diagonal e * diagonal hs.eigenvalues).trace ≤ 0 at ht
  rw [diagonal_mul_diagonal,trace_diagonal] at ht
  simpa [e,Finset.sum_ite_mem] using ht
end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset Set Filter Topology

private lemma closed_psd (b : ℕ) : IsClosed {T : Mat b | T.PosSemidef} := by
  have he : {T : Mat b | T.PosSemidef} =
      (⋂ i : Fin b, ⋂ j : Fin b, {T : Mat b | T i j=T j i}) ∩
      (⋂ x : Fin b → ℝ, {T : Mat b | 0 ≤ x ⬝ᵥ (T *ᵥ x)}) := by
    ext T
    simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    simp only [star_trivial]
    apply and_congr_left
    intro _
    exact ⟨fun h i j => by simpa using h.apply j i, fun h => Matrix.IsHermitian.ext fun i j => by simpa using h j i⟩
  rw [he]
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    unfold Matrix.mulVec dotProduct
    fun_prop

private lemma entry_bounded {b : ℕ} (T : Mat b) (ht : T.PosSemidef) (hu : (1-T).PosSemidef)
    (i j : Fin b) : -1 ≤ T i j ∧ T i j ≤ 1 := by
  have hd (k : Fin b) : T k k ≤ 1 := by
    have h := hu.diag_nonneg (i:=k)
    change 0≤(1:Mat b) k k - T k k at h
    rw [Matrix.one_apply_eq] at h
    exact sub_nonneg.mp h
  have hlo := ht.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have hhi := ht.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  have hs : T j i = T i j := by simpa using ht.1.apply i j
  simp only [star_trivial,mulVec_add,mulVec_sub,mulVec_single_one,add_dotProduct,sub_dotProduct,
    dotProduct_add,dotProduct_sub,single_dotProduct,one_mul,Matrix.col_apply,hs] at hlo hhi
  exact ⟨by linarith [hd i, hd j],by linarith [hd i, hd j]⟩

lemma isCompact_contractions (b : ℕ) :
    IsCompact {T : Mat b | T.PosSemidef ∧ (1-T).PosSemidef} := by
  let box : Set (Mat b) := Set.pi (Set.univ : Set (Fin b)) fun _ =>
      Set.pi (Set.univ : Set (Fin b)) fun _ => Set.Icc (-1:ℝ) 1
  have hbox : IsCompact box := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hc : IsClosed {T : Mat b | T.PosSemidef ∧ (1-T).PosSemidef} :=
    (closed_psd b).inter ((closed_psd b).preimage (continuous_const.sub continuous_id))
  apply hbox.of_isClosed_subset hc
  rintro T ⟨ht,hu⟩ i _ j _
  exact entry_bounded T ht hu i j
end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset
lemma compress_diag_le {n b : ℕ} (J : Matrix (Fin n) (Fin b) ℝ) (hJ : Jᵀ*J=1)
    (T : Mat b) (hT : (1-T).PosSemidef) (i : Fin n) : (J*T*Jᵀ) i i ≤ 1 := by
  let P := J*Jᵀ
  have hid : P*P=P := by
    change J*Jᵀ*(J*Jᵀ)=_
    rw [← Matrix.mul_assoc,Matrix.mul_assoc J Jᵀ J,hJ,Matrix.mul_one]
  have hself : Pᴴ=P := by change (J*Jᴴ)ᴴ=J*Jᴴ; simp
  have he : (1-P)*(1-P)ᴴ=1-P := by
    simp only [conjTranspose_sub,conjTranspose_one,hself,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_one,Matrix.one_mul,hid,sub_self,sub_zero]
  have h1 : (1-P).PosSemidef := he ▸ Matrix.posSemidef_self_mul_conjTranspose (1-P)
  have h2 : (P-J*T*Jᵀ).PosSemidef := by
    have hh := hT.mul_mul_conjTranspose_same J
    change (J*Jᴴ-J*T*Jᴴ).PosSemidef
    simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one] using hh
  have h := (h1.add h2).diag_nonneg (i:=i)
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.one_apply_eq] at h
  linarith
end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset Filter
open scoped Topology

private lemma diag_compress_nn {n b : ℕ} (J : Matrix (Fin n) (Fin b) ℝ) (T : Mat b)
    (hT : T.PosSemidef) (i : Fin n) : 0 ≤ (J*T*Jᵀ) i i := by
  exact (hT.mul_mul_conjTranspose_same J).diag_nonneg

private lemma max_log {n b : ℕ} (J : Matrix (Fin n) (Fin b) ℝ) (L ε : ℝ)
    (hL : 0<L) (hε : 0<ε) (hc : IsCompact {T : Mat b | T.PosSemidef ∧ (1-T).PosSemidef}) :
    ∃ T : Mat b, T.PosDef ∧ (1-T).PosSemidef ∧ ∀ S : Mat b, S.PosDef → (1-S).PosSemidef →
      L*Real.log S.det - ∑ i, Real.log ((J*S*Jᵀ) i i+ε) ≤
      L*Real.log T.det - ∑ i, Real.log ((J*T*Jᵀ) i i+ε) := by
  let F (T : Mat b) := T.det^L/(∏ i, ((J*T*Jᵀ) i i+ε))
  have hden (T : Mat b) (hT : T.PosSemidef) : 0< ∏ i, ((J*T*Jᵀ) i i+ε) :=
    prod_pos fun i _ => add_pos_of_nonneg_of_pos (diag_compress_nn J T hT i) hε
  have hone : (1 : Mat b).PosSemidef ∧ (1-(1 : Mat b)).PosSemidef := ⟨Matrix.PosSemidef.one,by rw [sub_self]; exact Matrix.PosSemidef.zero⟩
  have hF : ContinuousOn F {T : Mat b | T.PosSemidef ∧ (1-T).PosSemidef} := by
    apply ContinuousOn.div
    · exact ((Real.continuous_rpow_const (by positivity : 0 ≤ L)).comp continuous_id.matrix_det).continuousOn
    · apply Continuous.continuousOn
      fun_prop
    · intro T hT
      exact (hden T hT.1).ne'
  obtain ⟨T,hT,hmax⟩ := hc.exists_isMaxOn ⟨1,hone⟩ hF
  have hFp : 0<F T := lt_of_lt_of_le (show 0<F 1 by
    dsimp [F]; rw [Matrix.det_one,Real.one_rpow]; exact div_pos zero_lt_one (hden _ hone.1)) (hmax hone)
  have hdet : T.det≠0 := by
    intro h
    simp [F,h,Real.zero_rpow hL.ne'] at hFp
  have ht : T.PosDef := hT.1.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det T).mpr (isUnit_iff_ne_zero.mpr hdet))
  have hlog (S : Mat b) (hS : S.PosDef) : Real.log (F S) =
      L*Real.log S.det - ∑ i, Real.log ((J*S*Jᵀ) i i+ε) := by
    dsimp only [F]
    rw [Real.log_div (Real.rpow_pos_of_pos hS.det_pos _).ne' (hden S hS.posSemidef).ne',
      Real.log_rpow hS.det_pos,Real.log_prod (fun i _ => (add_pos_of_nonneg_of_pos
        (diag_compress_nn J S hS.posSemidef i) hε).ne')]
  refine ⟨T,ht,hT.2,fun S hs hcS => ?_⟩
  rw [← hlog S hs,← hlog T ht]
  exact Real.log_le_log (div_pos (Real.rpow_pos_of_pos hs.det_pos _) (hden S hs.posSemidef))
    (hmax (show S ∈ {T : Mat b | T.PosSemidef ∧ (1-T).PosSemidef} from ⟨hs.posSemidef,hcS⟩))

private lemma rankOne_det {b : ℕ} (K : Mat b) (s : ℝ) (v : Fin b → ℝ) :
    (K*(1+s • vecMulVec v v)*Kᵀ).det = (K*Kᵀ).det*(1+s*(v ⬝ᵥ v)) := by
  have h : s • vecMulVec v v = replicateCol (Fin 1) (s • v) * replicateRow (Fin 1) v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec, mul_assoc]
  have hd : ((1 : Mat b) + replicateCol (Fin 1) (s • v) * replicateRow (Fin 1) v).det =
      1 + v ⬝ᵥ (s • v) := Matrix.det_one_add_replicateCol_mul_replicateRow _ _
  calc
    _ = (K.det * ((1 : Mat b)+replicateCol (Fin 1) (s • v) * replicateRow (Fin 1) v).det)*Kᵀ.det := by rw [h,Matrix.det_mul,Matrix.det_mul]
    _ = _ := by rw [hd,Matrix.det_mul,dotProduct_smul,smul_eq_mul]; ring

private lemma ray_log_deriv {n : ℕ} (L q : ℝ) (h d : Fin n → ℝ) (hh : ∀ i, 0<h i) :
    HasDerivAt (fun t : ℝ => L*Real.log (1+t*q)-∑ i, Real.log (h i+t*d i))
      (L*q-∑ i, d i/h i) 0 := by
  have hlin (a b : ℝ) : HasDerivAt (fun t : ℝ => a+t*b) b 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const b).const_add a)
  have hlog (a b : ℝ) (ha : 0<a) : HasDerivAt (fun t : ℝ => Real.log (a+t*b)) (b/a) 0 := by
    simpa using (hlin a b).log (by simpa using ha.ne')
  apply HasDerivAt.sub
  · simpa using (hlog 1 q zero_lt_one).const_mul L
  · exact HasDerivAt.fun_sum fun i _ => hlog (h i) (d i) (hh i)

end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset Filter
open scoped Topology

private def ray {b : ℕ} (K : Mat b) (v : Fin b → ℝ) (s : ℝ) := K*(1+s • vecMulVec v v)*Kᵀ

private lemma ray_eq {b : ℕ} (K : Mat b) (v : Fin b → ℝ) (s : ℝ) :
    ray K v s = K*Kᵀ+s • vecMulVec (K*ᵥv) (K*ᵥv) := by
  rw [ray,mul_add,mul_one,add_mul,Matrix.mul_smul,Matrix.smul_mul,
    mul_vecMulVec,vecMulVec_mul,vecMul_transpose]

private lemma ray_diag {n b : ℕ} (J : Matrix (Fin n) (Fin b) ℝ) (K : Mat b)
    (v : Fin b → ℝ) (s : ℝ) (i : Fin n) :
    (J*ray K v s*Jᵀ) i i = (J*(K*Kᵀ)*Jᵀ) i i+s*(((J*K)*ᵥv) i)^2 := by
  rw [ray_eq,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
    mul_vecMulVec,vecMulVec_mul,vecMul_transpose,mulVec_mulVec]
  simp [vecMulVec_apply,sq]

private lemma ray_pd {b : ℕ} (K : Mat b) (hK : (K*Kᵀ).PosDef) (v : Fin b→ℝ) (s : ℝ)
    (hp : 0<1+s*(v ⬝ᵥ v)) : (ray K v s).PosDef := by
  have hv : (vecMulVec v v).PosSemidef := by simpa using Matrix.posSemidef_vecMulVec_self_star v
  have hI : ((1:Mat b)+s • vecMulVec v v).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_one.add (hv.1.smul (IsSelfAdjoint.all s)))
    intro x
    have he : star x ⬝ᵥ (((1:Mat b)+s • vecMulVec v v)*ᵥx) = x ⬝ᵥ x+s*(v ⬝ᵥ x)^2 := by
      simp only [star_trivial,add_mulVec,one_mulVec,Matrix.smul_mulVec,vecMulVec_mulVec,
        dotProduct_add,dotProduct_smul,smul_eq_mul,op_smul_eq_mul]
      rw [dotProduct_comm x v]
      ring
    rw [he]
    have hx : 0 ≤ x ⬝ᵥ x := sum_nonneg fun i _ => mul_self_nonneg _
    by_cases hs : 0 ≤ s
    · positivity
    · have hh : (v ⬝ᵥ x)^2 ≤ (v ⬝ᵥ v)*(x ⬝ᵥ x) := by
        simpa only [dotProduct,← sq] using Finset.sum_mul_sq_le_sq_mul_sq univ v x
      nlinarith only [mul_nonneg hp.le hx,mul_le_mul_of_nonpos_left hh (le_of_not_ge hs)]
  have hr : (ray K v s).PosSemidef := hI.mul_mul_conjTranspose_same K
  apply hr.posDef_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [isUnit_iff_ne_zero,ray,rankOne_det]
  exact mul_ne_zero hK.det_pos.ne' hp.ne'

private lemma ray_le {b : ℕ} (K : Mat b) (hc : (1-K*Kᵀ).PosSemidef) (v : Fin b→ℝ)
    {s : ℝ} (hs : s ≤ 0) : (1-ray K v s).PosSemidef := by
  have h : (vecMulVec (K*ᵥv) (K*ᵥv)).PosSemidef := by simpa using Matrix.posSemidef_vecMulVec_self_star (K*ᵥv)
  rw [ray_eq,sub_add_eq_sub_sub,sub_eq_add_neg,← neg_smul]
  exact hc.add (h.smul (neg_nonneg.mpr hs))

end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset Filter
open scoped Topology

private lemma stationary {n b : ℕ} (J : Matrix (Fin n) (Fin b) ℝ) (K : Mat b)
    (v : Fin b → ℝ) (L ε : ℝ) (hε : 0<ε) (hT : (K*Kᵀ).PosDef)
    (hc : (1-K*Kᵀ).PosSemidef)
    (hmax : ∀ S : Mat b, S.PosDef → (1-S).PosSemidef →
      L*Real.log S.det - ∑ i, Real.log ((J*S*Jᵀ) i i+ε) ≤
      L*Real.log (K*Kᵀ).det - ∑ i, Real.log ((J*(K*Kᵀ)*Jᵀ) i i+ε)) :
    let w := ∑ i, (((J*K)*ᵥv) i)^2/((J*(K*Kᵀ)*Jᵀ) i i+ε)
    w ≤ L*(v ⬝ᵥ v) ∧ ((∀ᶠ s : ℝ in 𝓝 0, (1-ray K v s).PosSemidef) → w=L*(v ⬝ᵥ v)) := by
  let q := v ⬝ᵥ v
  let h (i : Fin n) := (J*(K*Kᵀ)*Jᵀ) i i+ε
  let d (i : Fin n) := (((J*K)*ᵥv) i)^2
  let F (s : ℝ) := L*Real.log (1+s*q) - ∑ i, Real.log (h i+s*d i)
  let w := ∑ i,d i/h i
  have h0 : F 0 = -∑ i, Real.log (h i) := by simp [F]
  have hder : HasDerivAt F (L*q-w) 0 :=
    ray_log_deriv L q h d (fun i => add_pos_of_nonneg_of_pos (diag_compress_nn J _ hT.posSemidef i) hε)
  have hp : ∀ᶠ s : ℝ in 𝓝 0, 0<1+s*q :=
    (show ContinuousAt (fun s : ℝ => 1+s*q) 0 by fun_prop).eventually (lt_mem_nhds (by simp))
  have hopt : ∀ᶠ s : ℝ in 𝓝 0, (1-ray K v s).PosSemidef → F s ≤ F 0 := by
    filter_upwards [hp] with s hs
    intro hfe
    have hh := hmax _ (ray_pd K hT v s hs) hfe
    have hdet : (ray K v s).det = (K*Kᵀ).det*(1+s*q) := rankOne_det K s v
    rw [hdet,Real.log_mul hT.det_pos.ne' hs.ne'] at hh
    have hi (i : Fin n) : (J*ray K v s*Jᵀ) i i+ε = h i+s*d i := by
      rw [ray_diag]; dsimp [h,d]; ring
    simp_rw [hi] at hh
    rw [h0]
    change L*Real.log (1+s*q)-_ ≤ _
    linarith only [hh]
  constructor
  · have hh : 0 ≤ L*q-w := by
      apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hder).1
      filter_upwards [hopt.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hs hs0
      change s<0 at hs0
      rw [slope_def_field,sub_zero]
      exact div_nonneg_of_nonpos (sub_nonpos.mpr (hs (ray_le K hc v hs0.le))) hs0.le
    linarith
  · intro hf
    have hl : IsLocalMax F 0 := by
      filter_upwards [hopt,hf] with s hs hsp using hs hsp
    have he := hl.hasDerivAt_eq_zero hder
    linarith

end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset
private lemma count_contracted {n b : ℕ} (k m : ℕ) (hk : 1 ≤ k) (_hm : 1 ≤ m)
    (hb : b+m*(k-1)=n) (hr : m ≤ b) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε)
    (hsmall : (b:ℝ)*ε<(m:ℝ)*δ) (a g : Fin b → ℝ) (ha : ∀ j, 0 ≤ a j)
    (ha1 : ∀ j, a j ≤ 1) (ht : ∑ j,g j ≤ n)
    (hs : ∀ j, a j < 1 → g j=(k:ℝ)+δ) (hu : ∀ j, a j=1 → 1-ε ≤ g j) :
    ((b-m+1:ℕ):ℝ) ≤ ∑ j,a j := by
  let U := univ.filter fun j => a j < 1
  have hcard : U.card + Uᶜ.card=b := by
    have h := U.card_le_univ
    simp only [Fintype.card_fin] at h
    simp [card_compl,Nat.add_sub_of_le h]
  have hcc : (U.card:ℝ)+(Uᶜ.card:ℝ)=b := by exact_mod_cast hcard
  have hun (j : Fin b) (hj : j∈Uᶜ) : a j=1 := by
    apply le_antisymm (ha1 j)
    simpa [U] using hj
  have hsub : U.card < m := by
    by_contra! h
    have ht' : ((U.card:ℝ)*((k:ℝ)+δ)+(Uᶜ.card:ℝ)*(1-ε)) ≤ n := calc
      _ ≤ ∑ j ∈ U,g j + ∑ j ∈ Uᶜ,g j := by
        simp only [← nsmul_eq_mul,← sum_const]
        apply add_le_add
        · exact sum_le_sum fun j hj => (hs j (by simpa [U] using hj)).ge
        · exact sum_le_sum fun j hj => hu j (hun j hj)
      _ ≤ _ := by rw [sum_add_sum_compl]; exact ht
    have hmn : (m:ℝ) ≤ U.card := by exact_mod_cast h
    have hkb : (b:ℝ)+(m:ℝ)*((k:ℝ)-1)=n := by simpa [Nat.cast_sub hk] using (congrArg (Nat.cast : ℕ→ℝ) hb)
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hU : 0 ≤ (U.card:ℝ) := by positivity
    nlinarith only [ht',hsmall,hkb,hcc,mul_nonneg (sub_nonneg.mpr hmn) (sub_nonneg.mpr hk1),
      mul_nonneg (sub_nonneg.mpr hmn) hδ.le, mul_nonneg hU hε.le,
      congrArg (fun z : ℝ => z*ε) hcc]
  have hsize : b-m+1 ≤ Uᶜ.card := by omega
  calc
    _ ≤ (Uᶜ.card:ℝ) := by exact_mod_cast hsize
    _ = ∑ j ∈ Uᶜ,a j := by simp [sum_congr rfl (fun j hj => hun j hj)]
    _ ≤ _ := sum_le_univ_sum_of_nonneg ha

end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset Filter Unitary
open scoped Topology

private lemma spectral_factor {b : ℕ} (T : Mat b) (ht : T.PosDef) (hc : (1-T).PosSemidef) :
    ∃ (K : Mat b) (a : Fin b → ℝ), T=K*Kᵀ ∧ Kᵀ*K=Matrix.diagonal a ∧
      T.trace=∑ j,a j ∧ (∀ j,0≤a j) ∧ (∀ j,a j≤1) ∧
      ∀ j, a j<1 → ∀ᶠ s : ℝ in 𝓝 0, (1-ray K (Pi.single j 1) s).PosSemidef := by
  classical
  let U : Mat b := ht.1.eigenvectorUnitary
  let a := ht.1.eigenvalues
  let t (i : Fin b) := Real.sqrt (a i)
  let S := diagonal t
  let K := U*S
  have hU : Uᵀ*U=1 := ht.1.eigenvectorUnitary.2.1
  have hU' : U*Uᵀ=1 := ht.1.eigenvectorUnitary.2.2
  have hspec : T=U*diagonal a*Uᵀ := by
    have h : T=U*diagonal a*star U := by simpa [U,a,conjStarAlgAut_apply] using ht.1.spectral_theorem
    have hr : star U=Uᵀ := by ext i j; simp
    rwa [hr] at h
  have ha (i : Fin b) : 0 ≤ a i := ht.posSemidef.eigenvalues_nonneg i
  have hs (i : Fin b) : t i*t i=a i := Real.mul_self_sqrt (ha i)
  have hSS : S*S=diagonal a := by
    rw [show S=diagonal t from rfl,diagonal_mul_diagonal]
    exact congrArg diagonal (funext hs)
  have hST : Sᵀ=S := diagonal_transpose _
  have hcon : Uᵀ*T*U=diagonal a := by
    rw [hspec,←Matrix.mul_assoc,←Matrix.mul_assoc,hU,one_mul,Matrix.mul_assoc,hU,mul_one]
  have hbound : (1-diagonal a).PosSemidef := by
    have h := hc.conjTranspose_mul_mul_same U
    change (Uᵀ*(1-T)*U).PosSemidef at h
    rwa [mul_sub,mul_one,sub_mul,hU,hcon] at h
  have hmax (i : Fin b) : a i ≤ 1 := by
    have hh : 0≤(1-diagonal a) i i := hbound.diag_nonneg
    simpa using hh
  refine ⟨K,a,?_,?_,ht.1.trace_eq_sum_eigenvalues,ha,hmax,?_⟩
  · change T=(U*S)*(U*S)ᵀ
    rw [transpose_mul,hST,←Matrix.mul_assoc,Matrix.mul_assoc U S S,hSS,←hspec]
  · change (U*S)ᵀ*(U*S)=_
    rw [transpose_mul,hST,←Matrix.mul_assoc,Matrix.mul_assoc S Uᵀ U,hU,mul_one,hSS]
  intro j hj
  have ev : ∀ᶠ s : ℝ in 𝓝 0, a j*(1+s)<1 :=
    (continuous_const.mul (continuous_const.add continuous_id)).continuousAt.eventually_lt continuousAt_const (by simpa using hj)
  filter_upwards [ev] with s hjs
  let d (i : Fin b) : ℝ := if i=j then 1+s else 1
  have hm : (1+s • vecMulVec (Pi.single j (1:ℝ)) (Pi.single j (1:ℝ)) : Mat b)=diagonal d := by
    ext i k
    by_cases hi : i=j <;> by_cases hk : k=j <;> by_cases hik : i=k <;>
      simp_all [d,vecMulVec,Pi.single_apply]
  have hSD : S*diagonal d*S=diagonal (fun i => a i*d i) := by
    change diagonal t * diagonal d * diagonal t=_
    rw [diagonal_mul_diagonal,diagonal_mul_diagonal]
    congr 1
    funext i
    change t i * d i * t i = a i*d i
    rw [mul_right_comm,hs]
  have hRay : ray K (Pi.single j 1) s=U*diagonal (fun i=>a i*d i)*Uᵀ := by
    simp only [ray,K,hm,transpose_mul,hST,←hSD,Matrix.mul_assoc]
  have hdiag : (1-diagonal (fun i=>a i*d i) : Mat b).PosSemidef := by
    rw [←diagonal_one,diagonal_sub]
    apply posSemidef_diagonal_iff.mpr
    intro i
    by_cases hi : i=j <;> simp [d,hi,sub_nonneg,hjs.le,hmax]
  have hp := hdiag.mul_mul_conjTranspose_same U
  change (U*(1-diagonal (fun i=>a i*d i))*Uᵀ).PosSemidef at hp
  rwa [mul_sub,mul_one,sub_mul,hU',←hRay] at hp

end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset Filter
open scoped Topology

lemma approx_frame {n b : ℕ} (J : Matrix (Fin n) (Fin b) ℝ) (hJ : Jᵀ*J=1)
    (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (hb : b+m*(k-1)=n) (hr : m ≤ b)
    (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) (hsmall : (b:ℝ)*ε<(m:ℝ)*δ) :
    ∃ T K : Mat b, T.PosSemidef ∧ (1-T).PosSemidef ∧ ((b-m+1:ℕ):ℝ) ≤ T.trace ∧
      T=K*Kᵀ ∧ ∀ v : Fin b→ℝ, (∑ i, (((J*K)*ᵥv) i)^2/((J*T*Jᵀ) i i+ε)) ≤
        ((k:ℝ)+δ)*(∑ j,(v j)^2) := by
  obtain ⟨T,ht,hc,hmax⟩ := max_log J ((k:ℝ)+δ) ε (by positivity) hε (isCompact_contractions b)
  obtain ⟨K,a,rfl,hK,htr,ha0,ha1,hin⟩ := spectral_factor T ht hc
  let B := J*K
  let g (j : Fin b) := ∑ i, (B i j)^2/((J*(K*Kᵀ)*Jᵀ) i i+ε)
  have hR : B*Bᵀ = J*(K*Kᵀ)*Jᵀ := by simp [B, Matrix.transpose_mul,Matrix.mul_assoc]
  have hC : Bᵀ*B = diagonal a := by
    calc
      _ = Kᵀ*(Jᵀ*J)*K := by simp [B,Matrix.transpose_mul,Matrix.mul_assoc]
      _ = _ := by rw [hJ,mul_one,hK]
  have hrow (i : Fin n) : ∑ j,(B i j)^2 = (J*(K*Kᵀ)*Jᵀ) i i := by
    rw [← hR]
    simp [Matrix.mul_apply,sq]
  have hcol (j : Fin b) : ∑ i,(B i j)^2=a j := by
    have := congrArg (fun M : Mat b => M j j) hC
    simpa [Matrix.mul_apply,sq] using this
  have hg : ∑ j,g j ≤ n := by
    dsimp only [g]
    rw [sum_comm]
    calc
      _ ≤ ∑ _i : Fin n,(1:ℝ) := by
        apply sum_le_sum
        intro i _
        rw [← sum_div,hrow]
        exact (div_le_one (add_pos_of_nonneg_of_pos (diag_compress_nn J _ ht.posSemidef i) hε)).mpr (by linarith)
      _ = _ := by simp
  have hstat (j : Fin b) (h : a j<1) : g j=(k:ℝ)+δ := by
    have H := (stationary J K (Pi.single j 1) ((k:ℝ)+δ) ε hε ht hc hmax).2 (hin j h)
    simpa [g,B,Matrix.mulVec_single] using H
  have hlarge (j : Fin b) (h : a j=1) : 1-ε ≤ g j := by
    have hj : ∑ i,(B i j)^2=1 := (hcol j).trans h
    calc
      1-ε ≤ 1/(1+ε) := by
        apply (le_div_iff₀ (by linarith)).mpr
        nlinarith [sq_nonneg ε]
      _ = ∑ i,(B i j)^2/(1+ε) := by rw [← sum_div,hj]
      _ ≤ _ := by
        apply sum_le_sum
        intro i _
        exact div_le_div_of_nonneg_left (sq_nonneg _) (add_pos_of_nonneg_of_pos (diag_compress_nn J _ ht.posSemidef i) hε)
          (add_le_add (compress_diag_le J hJ _ hc i) le_rfl)
  refine ⟨K*Kᵀ,K,ht.posSemidef,hc,?_,rfl,?_⟩
  · rw [htr]
    exact count_contracted k m hk hm hb hr δ ε hδ hε hsmall a g ha0 ha1 hg hstat hlarge
  · intro v
    simpa only [dotProduct,← sq] using (stationary J K v ((k:ℝ)+δ) ε hε ht hc hmax).1
end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset Set Filter Topology

private lemma rectangular_bound {n b : ℕ} (B : Matrix (Fin n) (Fin b) ℝ)
    (d : Fin n → ℝ) (hd : ∀ i,0<d i) (L : ℝ) (hL : 0≤L)
    (hb : ∀ v : Fin b → ℝ,(∑ i, ((B *ᵥ v) i)^2 / (d i)) ≤ L*∑ j,(v j)^2) :
    (L • diagonal d-B*Bᵀ).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_,?_⟩
  · exact ((isHermitian_diagonal_iff.mpr fun _ => IsSelfAdjoint.all _).smul (IsSelfAdjoint.all _)).sub
      (isHermitian_mul_conjTranspose_self B)
  · intro x
    let v := Bᵀ *ᵥ x
    let S := ∑ j, (v j)^2
    let W := ∑ i, d i*(x i)^2
    have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hW : 0 ≤ W := Finset.sum_nonneg fun i _ => mul_nonneg (hd i).le (sq_nonneg _)
    have hid : x ⬝ᵥ (B *ᵥ v) = S := by
      rw [dotProduct_mulVec]
      change (x ᵥ* B) ⬝ᵥ v = _
      have he : x ᵥ* B=v := (mulVec_transpose B x).symm
      rw [he]
      simp [S,dotProduct,sq]
    have hcs : S^2 ≤ W* ∑ i, ((B *ᵥ v) i)^2/d i := by
      calc
        _ = (∑ i, x i*(B *ᵥ v) i)^2 := congrArg (·^2) hid.symm
        _ ≤ _ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
          (fun i _ => mul_nonneg (hd i).le (sq_nonneg _)) (fun i _ => div_nonneg (sq_nonneg _) (hd i).le)
          (fun i _ => by apply le_of_eq; field_simp [(hd i).ne'])
    have hbound : S ≤ L*W := by
      rcases hS.eq_or_lt with h|h
      · rw [← h]; exact mul_nonneg hL hW
      · apply le_of_mul_le_mul_right _ h
        calc
          S*S = S^2 := (sq _).symm
          _ ≤ _ := hcs.trans (mul_le_mul_of_nonneg_left (hb v) hW)
          _ = (L*W)*S := by ring
    have hw : x ⬝ᵥ (diagonal d *ᵥ x) = W := by
      simp only [mulVec_diagonal,dotProduct,W,sq]
      exact Finset.sum_congr rfl fun i _ => by ring
    change 0 ≤ x ⬝ᵥ ((L • diagonal d - B*Bᵀ)*ᵥ x)
    rw [sub_mulVec,smul_mulVec,← mulVec_mulVec,dotProduct_sub,dotProduct_smul,hw]
    apply sub_nonneg.mpr
    change x ⬝ᵥ (B *ᵥ v) ≤ L*W
    rwa [hid]

private lemma approximate_transfer {n b : ℕ} (J : Matrix (Fin n) (Fin b) ℝ)
    (T K : Mat b) (hT : T=K*Kᵀ) (ε L : ℝ) (hε : 0<ε) (hL : 0≤L)
    (h : ∀ v : Fin b → ℝ, (∑ i, (((J*K)*ᵥv) i)^2/((J*T*Jᵀ) i i+ε)) ≤ L*(∑ j,(v j)^2)) :
    (L • (diagPart (J*T*Jᵀ)+ ε • (1:Mat n)) - J*T*Jᵀ).PosSemidef := by
  let B := J*K
  let R := J*T*Jᵀ
  let d (i : Fin n) := R i i+ε
  have he : R = B*Bᵀ := by simp only [R,B,hT,transpose_mul,Matrix.mul_assoc]
  have hp : R.PosSemidef := he ▸ posSemidef_self_mul_conjTranspose B
  have hc := rectangular_bound B d (fun _ => add_pos_of_nonneg_of_pos hp.diag_nonneg hε) L hL h
  have diag : diagonal d=diagPart R+ε • (1:Mat n) := by
    ext i j
    by_cases hij : i=j <;> simp [d,diagPart,hij]
  rw [diag,← he] at hc
  exact hc

private lemma frame_contraction {n b : ℕ} (J : Matrix (Fin n) (Fin b) ℝ) (hJ : Jᵀ*J=1)
    (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (hb : b+m*(k-1)=n) (hr : m ≤ b) :
    ∃ T : Mat b,T.PosSemidef ∧ (1-T).PosSemidef ∧ ((b-m+1:ℕ):ℝ)≤T.trace ∧
      ((k:ℝ) • diagPart (J*T*Jᵀ) - J*T*Jᵀ).PosSemidef := by
  let δ (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  let ε (j : ℕ) : ℝ := δ j/((b:ℝ)+1)
  have hd j : 0<δ j := by dsimp [δ]; positivity
  have he j : 0<ε j := div_pos (hd j) (by positivity)
  have small j : (b:ℝ)*ε j < (m:ℝ)*δ j := by
    have hp : 0<(b:ℝ)+1 := by positivity
    have h1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hl : (b:ℝ)*ε j<δ j := by
      simp only [ε,mul_div_assoc']
      apply (div_lt_iff₀ hp).mpr
      nlinarith [hd j]
    exact hl.trans_le (by simpa using mul_le_mul_of_nonneg_right h1 (hd j).le)
  choose T K ht hu htr htk hq using fun j => approx_frame J hJ k m hk hm hb hr (δ j) (ε j) (hd j) (he j) (small j)
  let : FirstCountableTopology (Mat b) := inferInstanceAs (FirstCountableTopology (Fin b → Fin b → ℝ))
  obtain ⟨A,hA,φ,hφ,hlim⟩ := (isCompact_contractions b).isSeqCompact (fun j => ⟨ht j,hu j⟩)
  refine ⟨A,hA.1,hA.2,?_,?_⟩
  · have hc : Continuous fun M : Mat b => M.trace := continuous_id.matrix_trace
    exact ge_of_tendsto' (hc.continuousAt.tendsto.comp hlim) (fun j => htr (φ j))
  · let R (M : Mat b) := J*M*Jᵀ
    have cR : Continuous R := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have cD : Continuous (fun M : Mat n => diagPart M) :=
      (continuous_pi fun i => continuous_id.matrix_elem i i).matrix_diagonal
    have lr := cR.continuousAt.tendsto.comp hlim
    have ld := cD.continuousAt.tendsto.comp lr
    have dlim : Tendsto (δ ∘ φ) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have elim : Tendsto (ε ∘ φ) atTop (𝓝 0) := by
      simpa only [ε,Function.comp_def,zero_div] using dlim.div_const ((b:ℝ)+1)
    have l1 := elim.smul (tendsto_const_nhds (x:=(1:Mat n)))
    have l2 := (tendsto_const_nhds (x:=(k:ℝ))).add dlim
    have l3 := (l2.smul (ld.add l1)).sub lr
    simp only [add_zero,zero_smul] at l3
    apply (closed_psd n).mem_of_tendsto l3
    apply Filter.Eventually.of_forall
    intro j
    exact approximate_transfer J _ _ (htk (φ j)) _ _ (he _) (add_nonneg (Nat.cast_nonneg k) (hd _).le) (hq _)
end OMA.S_mo_334087

namespace OMA.S_mo_334087
open Matrix Finset Unitary

private lemma weighted_tail {b l : ℕ} (hl : l<b) (e w : Fin b → ℝ) (he : Antitone e)
    (hw : ∀ i, w i ∈ Set.Icc 0 1) (hmass : ((b-l : ℕ):ℝ) ≤ ∑ i,w i)
    (htrace : (∑ i, w i*e i) ≤ 0) :
    ∑ i ∈ univ.filter (fun i : Fin b => l ≤ i.val), e i ≤ 0 := by
  let S := univ.filter (fun i : Fin b => l ≤ i.val)
  let c := e ⟨l,hl⟩
  have htail (i : Fin b) (hi : i∈S) : e i ≤ c := he (by change l ≤ i.val; simpa [S] using hi)
  change (∑ i ∈ S,e i) ≤ 0
  by_cases hc : c ≤ 0
  · exact sum_nonpos fun i hi => (htail i hi).trans hc
  have hpoint (i : Fin b) : (if i∈S then e i-c else 0) ≤ w i*(e i-c) := by
    by_cases hi : i∈S
    · rw [if_pos hi]
      nlinarith [mul_nonneg (sub_nonneg.mpr (hw i).2) (sub_nonneg.mpr (htail i hi))]
    · rw [if_neg hi]
      have hfirst : i ≤ (⟨l,hl⟩ : Fin b) := by
        change i.val ≤ l
        have : ¬ l ≤ i.val := by simpa [S] using hi
        omega
      exact mul_nonneg (hw i).1 (sub_nonneg.mpr (he hfirst))
  have hsum := sum_le_sum (s:=univ) fun i _ => hpoint i
  have hcard : S.card=b-l := by
    have hL : S = univ \ (univ.filter (fun i : Fin b => i.val<l)) := by
      ext i; simp [S]
    simp [hL,card_sdiff_of_subset,Fin.card_filter_val_lt, min_eq_right hl.le]
  simp only [Finset.sum_ite_mem,univ_inter,sum_sub_distrib,sum_const,nsmul_eq_mul,
    mul_sub,←sum_mul,hcard] at hsum
  linarith [mul_le_mul_of_nonneg_right hmass (le_of_not_ge hc)]

private lemma interval_restrict {n b : ℕ} (hb : b ≤ n) (l : ℕ) (e : Fin n → ℝ) :
    (∑ i ∈ univ.filter (fun i : Fin n => l ≤ i.val ∧ i.val<b), e i) =
      ∑ i ∈ univ.filter (fun i : Fin b => l ≤ i.val),e (Fin.castLE hb i) := by
  symm
  apply Finset.sum_bij (fun i _ => Fin.castLE hb i)
  · intro i hi
    simpa using And.intro (show l ≤ i.val by simpa using hi) i.isLt
  · intro i _ j _ hij
    exact Fin.ext (congrArg (fun x : Fin n => x.val) hij)
  · intro j hj
    obtain ⟨hj₁,hj₂⟩ : l ≤ j.val ∧ j.val<b := by simpa using hj
    exact ⟨⟨j.val,hj₂⟩,by simpa using hj₁,Fin.ext rfl⟩
  · intros; rfl

lemma interval_of_frame {n : ℕ} (A : Mat n) (ha : A.PosSemidef) (k m : ℕ)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k*m ≤ n)
    (frame : ∀ {b : ℕ} (J : Matrix (Fin n) (Fin b) ℝ), Jᵀ*J=1 →
      b+m*(k-1)=n → m ≤ b → ∃ T : Mat b, T.PosSemidef ∧ (1-T).PosSemidef ∧
        ((b-m+1 : ℕ):ℝ) ≤ T.trace ∧
          ((k:ℝ) • diagPart (J*T*Jᵀ) - (J*T*Jᵀ)).PosSemidef) :
    ∑ i ∈ univ.filter (fun i : Fin (Fintype.card (Fin n)) =>
        m-1 ≤ i.val ∧ i.val<n-m*(k-1)), (shiftedHerm ha k).eigenvalues₀ i ≤ 0 := by
  classical
  let H := shifted A k
  let hs := shiftedHerm ha k
  let U := hs.eigenvectorUnitary
  let b := n-m*(k-1)
  have hspan : m*(k-1)+m = k*m := by
    calc
      _ = m*((k-1)+1) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hk,Nat.mul_comm]
  have heqb : b+m*(k-1)=n := by dsimp [b]; omega
  have hmb : m ≤ b := by omega
  have hbn : b ≤ Fintype.card (Fin n) := by simp [b]
  let E := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  let q (i : Fin b) : Fin n := E (Fin.castLE hbn i)
  let e (i : Fin b) := hs.eigenvalues₀ (Fin.castLE hbn i)
  have eqv (i : Fin b) : hs.eigenvalues (q i) = e i := by simp [q,e,E,Matrix.IsHermitian.eigenvalues]
  let J : Matrix (Fin n) (Fin b) ℝ := (U : Mat n).submatrix id q
  have hUU : (U : Mat n)ᵀ*(U : Mat n)=1 := U.2.1
  have hinj : Function.Injective q := E.injective.comp (fun _ _ h => Fin.ext (congrArg (fun x : Fin (Fintype.card (Fin n)) => x.val) h))
  have hJ : Jᵀ*J=1 := by
    have he : Jᵀ*J = ((U : Mat n)ᵀ*(U : Mat n)).submatrix q q := by ext i j; rfl
    rw [he,hUU]
    ext i j
    simp [Matrix.one_apply,hinj.eq_iff]
  have hspec : H= (U : Mat n)*diagonal hs.eigenvalues*star (U : Mat n) := by
    simpa [U,conjStarAlgAut_apply] using hs.spectral_theorem
  have hHU : H*(U : Mat n) = (U : Mat n)*diagonal hs.eigenvalues := by
    rw [hspec,Matrix.mul_assoc,Unitary.coe_star_mul_self,Matrix.mul_one]
  have hHJ : H*J=J*diagonal e := by
    have he : H*J = (H*(U : Mat n)).submatrix id q := by ext i j; rfl
    rw [he,hHU]
    ext i j
    simp [J,Matrix.mul_diagonal,eqv]
  obtain ⟨T,hT,hIT,htr,hR⟩ := frame J hJ heqb hmb
  have ht := trace_shift A _ k ha hR
  change ((J*T*Jᵀ)*H).trace ≤ 0 at ht
  have hmult : ((J*T*Jᵀ)*H).trace=(T*diagonal e).trace := by
    rw [Matrix.mul_assoc,trace_mul_comm,← Matrix.mul_assoc,Matrix.mul_assoc Jᵀ H J,hHJ,
      ←Matrix.mul_assoc Jᵀ J,hJ,one_mul,trace_mul_comm]
  rw [hmult] at ht
  change (∑ i, (T * diagonal e) i i) ≤ 0 at ht
  simp only [Matrix.mul_diagonal] at ht
  change (∑ i ∈ univ.filter (fun i : Fin (Fintype.card (Fin n)) =>
    m-1 ≤ i.val ∧ i.val<b),hs.eigenvalues₀ i) ≤ 0
  rw [interval_restrict hbn]
  apply weighted_tail (show m-1<b by omega) e (fun i=>T i i) (fun {i j} hij => hs.eigenvalues₀_antitone (show Fin.castLE hbn i ≤ Fin.castLE hbn j from hij))
  · intro i
    have hh : 0 ≤ (1-T) i i := hIT.diag_nonneg
    simp at hh
    exact ⟨hT.diag_nonneg,by linarith⟩
  · change ((b-(m-1):ℕ):ℝ) ≤ T.trace
    rwa [show b-(m-1)=b-m+1 by omega]
  · exact ht

end OMA.S_mo_334087

open OMA.S_mo_334087
theorem OMA.solution : type_of% @OMA.S_mo_334087.main := by
  refine ⟨fun _ => projection_bound,fun _ A ha k =>
    ⟨shiftedHerm ha k,fun S hc => eigen_sum A ha k S hc (fun P => projection_bound P)⟩,?_⟩
  intro n A ha k m hk hm
  refine ⟨shiftedHerm ha k,?_⟩
  by_cases hkm : k*m ≤ n
  · exact interval_of_frame A ha k m hk hm hkm (fun J hJ hb hr => frame_contraction J hJ k m hk hm hb hr)
  · have hmul : m*(k-1)+m=k*m := by
      calc
        _ = m*((k-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
        _ = k*m := by rw [Nat.sub_add_cancel hk,Nat.mul_comm]
    have he : Finset.univ.filter (fun i : Fin (Fintype.card (Fin n)) =>
        m-1 ≤ i.val ∧ i.val < n-m*(k-1)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _
      omega
    simp only [he,Finset.sum_empty,le_refl]
