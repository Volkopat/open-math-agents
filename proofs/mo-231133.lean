import OMAStatements.S_mo_231133

/-!
Complete proof by @connoranderson, linked from statement PR #24791 and desk DONE #113865.
Pinned source: https://github.com/connoranderson/open-math-agents/blob/9dba4d86a8ad9a2f413d565f773dfb01c96998e6/proofs/mo-231133.lean
All mathematical source unchanged; this port adds provenance and current-checker validation.
Credit Bullmoose's original question https://mathoverflow.net/questions/231133 (CC BY-SA 3.0)
and the classical Mirsky trace-norm inequality. Port and validation: @rodolfoquint.
-/

namespace OMA.S_mo_231133

open Matrix Module
open scoped InnerProductSpace ComplexOrder

private lemma common_vector {N : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b c : OrthonormalBasis (Fin N) ℂ E) (i : Fin N) :
    ∃ x : E, x ≠ 0 ∧ (∀ j, i < j → b.repr x j = 0) ∧
      (∀ j, j < i → c.repr x j = 0) := by
  let pad : (Fin (i.val+1) → ℂ) →ₗ[ℂ] (Fin N → ℂ) :=
    { toFun := fun a j => if h : j ≤ i then a ⟨j.val,Nat.lt_succ_of_le h⟩ else 0
      map_add' := fun x y => by ext j; by_cases h : j ≤ i <;> simp [h]
      map_smul' := fun s x => by ext j; by_cases h : j ≤ i <;> simp [h] }
  let lift := b.repr.symm.toLinearEquiv.toLinearMap.comp
    (((WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).symm.toLinearMap).comp pad)
  let test : (Fin (i.val+1) → ℂ) →ₗ[ℂ] (Fin i.val → ℂ) :=
    LinearMap.pi fun j => (c.toBasis.coord ⟨j.val,lt_trans j.isLt i.isLt⟩).comp lift
  have hker : test.ker ≠ ⊥ := by
    intro h
    have hk := test.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp h)
    simp at hk
  simp only [ne_eq, LinearMap.ker_eq_bot'] at hker
  push Not at hker
  obtain ⟨a,ha,ha0⟩ := hker
  have hb (j : Fin N) : b.repr (lift a) j = pad a j := by
    simp [lift]
  refine ⟨lift a, ?_, ?_, ?_⟩
  · intro h
    apply ha0
    ext j
    let k : Fin N := ⟨j.val,lt_of_lt_of_le j.isLt i.isLt⟩
    have hk := hb k
    have hkj : k ≤ i := Nat.le_of_lt_succ j.isLt
    simpa [h,pad,hkj,k] using hk.symm
  · intro j hj
    rw [hb]
    simp [pad, not_le.mpr hj]
  · intro j hj
    exact congrFun ha ⟨j.val,hj⟩

private lemma spectral_rayleigh {N : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E)
    (hT : T.IsSymmetric) (hN : finrank ℂ E = N) (x : E) :
    (⟪x,T x⟫_ℂ).re = ∑ j, hT.eigenvalues hN j * ‖(hT.eigenvectorBasis hN).repr x j‖^2 := by
  let b := hT.eigenvectorBasis hN
  rw [← b.repr.inner_map_map x (T x), EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ((b.repr (T x) j) * star (b.repr x j)).re = _
  rw [show b.repr (T x) j = (hT.eigenvalues hN j : ℂ) * b.repr x j from
    hT.eigenvectorBasis_apply_self_apply hN x j, mul_assoc]
  simp [b, Complex.mul_conj, Complex.sq_norm]

lemma eigen_mono {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : (B-A).PosSemidef)
    (i : Fin (Fintype.card (Fin n))) : hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i := by
  let T := A.toEuclideanLin
  let U := B.toEuclideanLin
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hU : U.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hN : finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := finrank_euclideanSpace
  let b := hT.eigenvectorBasis hN
  let c := hU.eigenvectorBasis hN
  obtain ⟨x,hx,hb,hc⟩ := common_vector b c i
  have en (e : OrthonormalBasis (Fin (Fintype.card (Fin n))) ℂ (EuclideanSpace ℂ (Fin n))) :
      ‖x‖^2 = ∑ j, ‖e.repr x j‖^2 := by rw [← e.repr.norm_map x, EuclideanSpace.norm_sq_eq]
  have hm : (⟪x,T x⟫_ℂ).re ≤ (⟪x,U x⟫_ℂ).re := by
    have hh := h.re_dotProduct_nonneg x.ofLp
    rw [sub_mulVec, dotProduct_sub] at hh
    change ((A *ᵥ x.ofLp) ⬝ᵥ star x.ofLp).re ≤ ((B *ᵥ x.ofLp) ⬝ᵥ star x.ofLp).re
    rw [dotProduct_comm (A *ᵥ _), dotProduct_comm (B *ᵥ _)]
    exact sub_nonneg.mp hh
  have lo : hT.eigenvalues hN i * ‖x‖^2 ≤ (⟪x,T x⟫_ℂ).re := by
    rw [en b, spectral_rayleigh T hT hN, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : j ≤ i
    · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hN hij) (sq_nonneg _)
    · change _ ≤ _ * ‖b.repr x j‖^2
      simp [hb j (lt_of_not_ge hij)]
  have hi : (⟪x,U x⟫_ℂ).re ≤ hU.eigenvalues hN i * ‖x‖^2 := by
    rw [en c, spectral_rayleigh U hU hN, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i ≤ j
    · exact mul_le_mul_of_nonneg_right (hU.eigenvalues_antitone hN hij) (sq_nonneg _)
    · change _ * ‖c.repr x j‖^2 ≤ _
      simp [hc j (lt_of_not_ge hij)]
  exact le_of_mul_le_mul_right (lo.trans (hm.trans hi)) (sq_pos_of_pos (norm_pos_iff.mpr hx))

end OMA.S_mo_231133

namespace OMA.S_mo_231133
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

private lemma eig_sum {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    ∑ i, hA.eigenvalues₀ i = A.trace.re := by
  rw [hA.trace_eq_sum_eigenvalues,Complex.re_sum]
  simp only [IsHermitian.eigenvalues]
  exact (Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm hA.eigenvalues₀).symm

private lemma mirsky {n : ℕ} {A D : Mat n} (hA : A.IsHermitian) (hD : D.IsHermitian) :
    lower hA hD ≤ nuclear (A-D) := by
  let C := A-D
  have hC : IsSelfAdjoint C := hA.sub hD
  let Z := D+C⁺
  have hZ : Z.IsHermitian := hD.add (CFC.posPart_nonneg C).isSelfAdjoint
  have hP : C⁺-C⁻=C := CFC.posPart_sub_negPart C hC
  have hN : C⁺+C⁻=CFC.abs C := CFC.posPart_add_negPart C hC
  have hdE : Z-D=C⁺ := by dsimp [Z]; abel
  have haE : Z-A=C⁻ := by
    calc
      Z-A = C⁺-C := by dsimp [Z,C]; abel
      _ = C⁻ := by rw [sub_eq_iff_eq_add.mp hP]; abel
  have hdZ : (Z-D).PosSemidef := hdE ▸ (CFC.posPart_nonneg C).posSemidef
  have haZ : (Z-A).PosSemidef := haE ▸ (CFC.negPart_nonneg C).posSemidef
  have hb : lower hA hD ≤ ∑ i, ((hZ.eigenvalues₀ i-hA.eigenvalues₀ i)+(hZ.eigenvalues₀ i-hD.eigenvalues₀ i)) := by
    apply Finset.sum_le_sum
    intro i _
    have h1 := eigen_mono hA hZ haZ i
    have h2 := eigen_mono hD hZ hdZ i
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  refine hb.trans_eq ?_
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,eig_sum]
  have he : (Z-A)+(Z-D) = CFC.abs C := by
    rw [haE,hdE,←hN,add_comm]
  exact (by simpa [nuclear,C,Matrix.trace_add,Matrix.trace_sub] using congrArg (fun M : Mat n => M.trace.re) he)

end OMA.S_mo_231133

namespace OMA.S_mo_231133
open Matrix Unitary
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexConjugate ComplexOrder

private lemma nuclear_conjugate_diagonal {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ)
    (a : Fin n → ℝ) :
    nuclear (conjStarAlgAut ℂ (Mat n) u (diagonal fun i => (a i : ℂ))) = ∑ i, |a i| := by
  let F := conjStarAlgAut ℂ (Mat n) u
  let A : Mat n := diagonal fun i => (a i : ℂ)
  let D : Mat n := diagonal fun i => ((|a i| : ℝ) : ℂ)
  have hD : D.PosSemidef := posSemidef_diagonal_iff.mpr (by intro i; simp)
  have hA : star A = A := by simp [A,Matrix.star_eq_conjTranspose]
  have hs : D*D=A*A := by
    simp only [D,A,diagonal_mul_diagonal]
    congr 1
    funext i
    rw [←Complex.ofReal_mul,←Complex.ofReal_mul,abs_mul_abs_self]
  have hpos : 0≤F D := (hD.mul_mul_conjTranspose_same (u : Mat n)).nonneg
  have ha : CFC.abs (F A) = F D := by
    apply CFC.sqrt_unique _ hpos
    rw [←map_mul,←map_star,hA,←map_mul,hs]
  change (CFC.abs (F A)).trace.re = _
  rw [ha]
  simp only [F,conjStarAlgAut_apply,trace_mul_cycle,coe_star_mul_self,one_mul,D,
    trace_diagonal,Complex.re_sum,Complex.ofReal_re]

lemma sharp {n : ℕ} {A D : Mat n} (hA : A.IsHermitian) (hD : D.IsHermitian) :
    ∃ U : Matrix.unitaryGroup (Fin n) ℂ, nuclear (A - (U : Mat n)*D*(U : Mat n)ᴴ)=lower hA hD := by
  classical
  let U := hA.eigenvectorUnitary * star hD.eigenvectorUnitary
  refine ⟨U,?_⟩
  have he : (U : Mat n)*D*(U : Mat n)ᴴ =
      conjStarAlgAut ℂ (Mat n) hA.eigenvectorUnitary
        (diagonal (RCLike.ofReal ∘ hD.eigenvalues)) := by
    change conjStarAlgAut ℂ (Mat n) U D = _
    dsimp only [U]
    rw [conjStarAlgAut_mul_apply,hD.conjStarAlgAut_star_eigenvectorUnitary]
  rw [he]
  have hc := congrArg (fun M => nuclear (M -
    conjStarAlgAut ℂ (Mat n) hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hD.eigenvalues))))
    hA.spectral_theorem
  refine hc.trans ?_
  rw [←map_sub,diagonal_sub]
  have hh := nuclear_conjugate_diagonal hA.eigenvectorUnitary (fun i => hA.eigenvalues i-hD.eigenvalues i)
  simp only [Complex.ofReal_sub] at hh
  refine hh.trans ?_
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm
    (fun i => |hA.eigenvalues₀ i - hD.eigenvalues₀ i|)
end OMA.S_mo_231133

namespace OMA.S_mo_231133
open Matrix
open scoped ComplexConjugate

private lemma real_case {n : ℕ} (A B : Mat n) (s : ℝ) :
    mix A (s:ℂ) B = A - (-(s • (B+Bᴴ))) := by
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) s (B+Bᴴ)]
  simp only [mix,sub_neg_eq_add,smul_add,add_assoc]
  rw [show star (s:ℂ) = (s:ℂ) from Complex.conj_ofReal s]
  rfl

private lemma nonreal_case {n : ℕ} (A : Mat n) (hA : A.IsHermitian)
    (b : ℂ) (hb : b.im≠0) (H T : Mat n) (hH : H.IsHermitian) (hT : T.IsHermitian) :
    (∃ B : Mat n, B+Bᴴ = H ∧ mix A b B = T ∧ ¬ B.IsHermitian) ↔ T ≠ A+b.re • H := by
  have hbc : b-star b ≠ 0 := by
    intro hz
    have := congrArg Complex.im hz
    simp at this
    exact hb (by linarith)
  have hcoef : star b = (2:ℂ)*(b.re:ℂ)-b := by
    apply Complex.ext
    · simp; ring
    · simp
  have hre := RCLike.real_smul_eq_coe_smul (K:=ℂ) (E:=Mat n) b.re
  have hdiff (B : Mat n) :
      mix A b B - (A+b.re • (B+Bᴴ)) = (b-(b.re:ℂ)) • (B-Bᴴ) := by
    rw [hre]
    unfold mix
    rw [hcoef]
    module
  have hbr : b-(b.re:ℂ) ≠ 0 := by
    intro h
    have he := congrArg Complex.im h
    simp at he
    exact hb he
  constructor
  · rintro ⟨B,hBH,hBT,hB⟩ he
    have hh := hdiff B
    rw [hBH,hBT,he,sub_self] at hh
    have hz := (smul_eq_zero.mp hh.symm).resolve_left hbr
    exact hB (sub_eq_zero.mp hz).symm
  · intro hne
    let c := (b-star b)⁻¹
    let B := c • (T-A-(star b) • H)
    have hsc : star c = -c := by
      change star ((b-star b)⁻¹) = -((b-star b)⁻¹)
      rw [star_inv₀,star_sub,star_star,← neg_sub b (star b),inv_neg]
    have ha : Bᴴ = -c • (T-A-b • H) := by
      simp [B,Matrix.conjTranspose_smul,hT.eq,hA.eq,hH.eq,hsc]
    have hch : c*(b-star b)=1 := inv_mul_cancel₀ hbc
    have hsum : B+Bᴴ=H := by
      rw [ha]
      dsimp only [B]
      calc
        _ = (c*(b-star b)) • H := by module
        _ = _ := by rw [hch,one_smul]
    have hmix : mix A b B=T := by
      rw [mix,ha]
      dsimp only [B]
      calc
        _ = A + (c*(b-star b)) • (T-A) := by module
        _ = _ := by rw [hch,one_smul]; abel
    refine ⟨B,hsum,hmix,?_⟩
    intro he
    have hh := hdiff B
    rw [hsum,hmix,he.eq,sub_self,smul_zero] at hh
    exact hne (sub_eq_zero.mp hh)

end OMA.S_mo_231133

open OMA.S_mo_231133

theorem OMA.solution : type_of% @OMA.S_mo_231133.main := by
  intro n A hA
  exact ⟨fun D hD => ⟨mirsky hA hD,sharp hA hD⟩,fun s B => real_case A B s,
    fun b hb H T hH hT => nonreal_case A hA b hb H T hH hT⟩
