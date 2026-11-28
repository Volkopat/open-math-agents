import OMAStatements.S_mo_354536

namespace OMA.S_mo_354536
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

private lemma perm_unitary {n} (σ : Perm n) : σ.permMatrix ℂ ∈ unitary (Mat n) := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (σ.permMatrix ℂ)ᴴ * σ.permMatrix ℂ=1
  rw [Matrix.conjTranspose_permMatrix,← Matrix.permMatrix_mul,mul_inv_cancel,Matrix.permMatrix_one]

private lemma adjoint_inter {n} {X A P : Mat n} (ha : A ∈ unitary (Mat n))
    (hp : P ∈ unitary (Mat n)) (h : X*A=P*X) : A*star X=star X*P := by
  have hh := congrArg star h
  simp only [star_mul] at hh
  calc
    A*star X = (A*star X)*(star P*P) := by rw [hp.1,mul_one]
    _ = A*(star X*star P)*P := by simp only [mul_assoc]
    _ = A*(star A*star X)*P := by rw [←hh]
    _ = star X*P := by rw [←mul_assoc,ha.2,one_mul]

private lemma polar {n} {A B P Q X : Mat n} (ha : A ∈ unitary (Mat n)) (hb : B ∈ unitary (Mat n))
    (hp : P ∈ unitary (Mat n)) (hq : Q ∈ unitary (Mat n))
    (hx : IsUnit X) (h₁ : X*A=P*X) (h₂ : X*B=Q*X) :
    ∃ U : unitary (Mat n), (U:Mat n)*A=P*(U:Mat n) ∧ (U:Mat n)*B=Q*(U:Mat n) := by
  let H := star X*X
  let S := CFC.sqrt H
  have hn : 0 ≤ H := star_mul_self_nonneg X
  have hsq : S*S=H := CFC.sqrt_mul_sqrt_self H hn
  have hs : IsUnit S := (CFC.isUnit_sqrt_iff H hn).mpr (hx.star.mul hx)
  have hd := (Matrix.isUnit_iff_isUnit_det S).mp hs
  have hself : Sᴴ=S := (CFC.sqrt_nonneg H).isSelfAdjoint
  have hunit : X*S⁻¹ ∈ unitary (Mat n) := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [star_mul]
    change S⁻¹ᴴ * star X * (X*S⁻¹)=1
    rw [Matrix.conjTranspose_nonsing_inv,hself]
    calc
      S⁻¹ * star X * (X*S⁻¹) = S⁻¹*H*S⁻¹ := by simp only [H,mul_assoc]
      _ = S⁻¹*(S*S)*S⁻¹ := by rw [hsq]
      _ = 1 := by rw [←mul_assoc,S.nonsing_inv_mul hd,one_mul,S.mul_nonsing_inv hd]
  have step (A P : Mat n) (hu : A ∈ unitary (Mat n)) (hv : P ∈ unitary (Mat n)) (h : X*A=P*X) :
      (X*S⁻¹)*A=P*(X*S⁻¹) := by
    have hc : Commute H A := by
      change (star X*X)*A=A*(star X*X)
      rw [mul_assoc,h,←mul_assoc,←adjoint_inter hu hv h,mul_assoc]
    have hsc : Commute S A := by
      dsimp only [S]
      rw [CFC.sqrt_eq_cfc]
      exact hc.cfc_nnreal _
    have hci : S⁻¹*A=A*S⁻¹ := by
      calc
        S⁻¹*A = S⁻¹*(A*S)*S⁻¹ := by simp only [mul_assoc,S.mul_nonsing_inv hd,mul_one]
        _ = S⁻¹*(S*A)*S⁻¹ := by rw [hsc.eq]
        _ = A*S⁻¹ := by rw [←mul_assoc,S.nonsing_inv_mul hd,one_mul]
    rw [mul_assoc,hci,←mul_assoc,h,mul_assoc]
  exact ⟨⟨_,hunit⟩,step A P ha hp h₁,step B Q hb hq h₂⟩

open MvPolynomial Finset

private lemma eval_pencil {n d} (v : Fin d → Mat n) (x : Fin d → ℂ) :
    MvPolynomial.eval x (pencil v) = (∑ l, x l • v l).det := by
  rw [pencil,RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map,Matrix.sum_apply,Matrix.smul_apply]

private lemma pencil_degree {n d} (v : Fin d → Mat n) : (pencil v).totalDegree ≤ n := by
  classical
  rw [pencil,Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro σ _
  refine (totalDegree_mul ..).trans ?_
  have hc (k : ℤ) : (k : MvPolynomial (Fin d) ℂ).totalDegree=0 := by
    rw [← map_intCast (C : ℂ →+* MvPolynomial (Fin d) ℂ) k,totalDegree_C]
  rw [hc,zero_add]
  refine (totalDegree_finsetProd ..).trans ?_
  calc
    _ ≤ ∑ _ : Fin n, (1:ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Matrix.of_apply]
      apply totalDegree_finsetSum_le
      intro l _
      simpa using totalDegree_mul (X l : MvPolynomial (Fin d) ℂ) (C (v l (σ i) i))
    _ = n := by simp

private lemma sampled {n d} (v : Fin d → Mat n) : pencil v ≠ 0 ↔
    ∃ x : Fin d → Fin (n+1), (∑ i, (x i : ℂ) • v i).det ≠ 0 := by
  classical
  constructor
  · intro hp
    let S : Finset ℂ := (univ : Finset (Fin (n+1))).image (fun i : Fin (n+1) => (i.val:ℂ))
    have on_grid (z : ℂ) (hz : z∈S) : ∃ j : Fin (n+1), (j:ℂ)=z := by
      simpa only [S,mem_image,mem_univ,true_and] using hz
    have hin : Function.Injective (fun i : Fin (n+1) => (i:ℂ)) := by
      intro i j h
      change (i.val:ℂ)=(j.val:ℂ) at h
      exact Fin.ext (by exact_mod_cast h)
    have hs : S.card=n+1 := by simp [S,Finset.card_image_of_injective _ hin]
    have ne : (S.card:ℚ≥0) ≠ 0 := by rw [hs];positivity
    by_contra! h
    have vanish (x : Fin d→ℂ) (hx : x∈Fintype.piFinset (fun _ : Fin d => S)) : eval x (pencil v)=0 := by
      have he (i : Fin d) : ∃ j : Fin (n+1), (j:ℂ)=x i := by
        exact on_grid _ ((Fintype.mem_piFinset (t:=fun _ : Fin d => S) (f:=x)).mp hx i)
      choose t ht using he
      rw [eval_pencil,← funext ht]
      exact h t
    have hz := schwartz_zippel_totalDegree hp S
    rw [Finset.filter_true_of_mem vanish] at hz
    rw [Fintype.card_piFinset_const,Nat.cast_pow,div_self (pow_ne_zero d ne)] at hz
    have hdeg : (S.card:ℚ≥0) ≤ (pencil v).totalDegree := by
      simpa using (le_div_iff₀ (pos_iff_ne_zero.mpr ne)).mp hz
    have hn := pencil_degree v
    have : S.card ≤ (pencil v).totalDegree := by exact_mod_cast hdeg
    omega
  · rintro ⟨x,h⟩ hz
    have he := eval_pencil v (fun i => (x i:ℂ))
    rw [hz,map_zero] at he
    exact h he.symm


private lemma common_criterion {n} {A B : Mat n} (ha : A∈unitary (Mat n)) (hb : B∈unitary (Mat n))
    (bases : ∀ σ τ, BasisFor A B σ τ) :
    common A B ↔ ∃ σ τ : Perm n, pencil (basisMatrices (bases σ τ)) ≠ 0 := by
  classical
  constructor
  · rintro ⟨U,σ,τ,h₁,h₂⟩
    have hi (A P : Mat n) (h : (U:Mat n)*A*(U:Mat n)ᴴ=P) : (U:Mat n)*A=P*(U:Mat n) := by
      rw [←h,Matrix.mul_assoc _ (U:Mat n)ᴴ]
      change _=_*(star (U:Mat n)*(U:Mat n))
      rw [U.prop.1,Matrix.mul_one]
    let X : inter A B σ τ := ⟨(U:Mat n),hi _ _ h₁,hi _ _ h₂⟩
    let b := bases σ τ
    have hsum : (∑ i, b.repr X i • basisMatrices (bases σ τ) i)=(U:Mat n) := by
      simpa only [Submodule.coe_sum,Submodule.coe_smul_of_tower,basisMatrices,b,X] using congrArg (fun M : inter A B σ τ => (M:Mat n)) (b.sum_repr X)
    refine ⟨σ,τ,?_⟩
    intro hz
    have he := eval_pencil (basisMatrices (bases σ τ)) (fun i => b.repr X i)
    rw [hz,map_zero,hsum] at he
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (Unitary.isUnit_coe (U:=U))).ne_zero he.symm
  · rintro ⟨σ,τ,hp⟩
    obtain ⟨x,hx⟩ := (sampled _).mp hp
    let M := inter A B σ τ
    let b := bases σ τ
    let Y : M := ∑ i, (x i:ℂ) • b i
    have he : (Y:Mat n) = ∑ i,(x i:ℂ) • basisMatrices (bases σ τ) i := by simp [Y,b,M,basisMatrices]
    have hy := Y.prop
    change (Y:Mat n)*A=σ.permMatrix ℂ*(Y:Mat n) ∧ (Y:Mat n)*B=τ.permMatrix ℂ*(Y:Mat n) at hy
    have hu : IsUnit (Y:Mat n) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (he ▸ hx))
    obtain ⟨U,h₁,h₂⟩ := polar ha hb (perm_unitary σ) (perm_unitary τ) hu hy.1 hy.2
    have conj (A P : Mat n) (h : (U:Mat n)*A=P*(U:Mat n)) : (U:Mat n)*A*(U:Mat n)ᴴ=P := by
      rw [h,Matrix.mul_assoc]
      change P*((U:Mat n)*star (U:Mat n))=P
      rw [U.prop.2,Matrix.mul_one]
    exact ⟨U,σ,τ,conj _ _ h₁,conj _ _ h₂⟩
end OMA.S_mo_354536
open OMA.S_mo_354536

theorem OMA.solution : type_of% @OMA.S_mo_354536.main := by
  intro n A B ha hb bases
  exact ⟨common_criterion ha hb bases,(common_criterion ha hb bases).trans (exists_congr fun σ => exists_congr fun τ => sampled _)⟩
