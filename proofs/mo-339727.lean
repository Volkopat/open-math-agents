import OMAStatements.S_mo_339727

namespace OMA.S_mo_339727
open Matrix Finset
open scoped Matrix.Norms.L2Operator MatrixOrder

set_option maxHeartbeats 800000 in
private lemma window_near_scalar {n : ℕ} [Nonempty (Fin n)] (E : Mat n) {R : ℝ} (hr : 0 < R) (hE : ‖E‖ ≤ R/8) :
    let t := 3*R/2
    let M := t • (1:Mat n)+E
    ∀ z ∈ spectrum ℝ (Mᵀ*M), R^2 < z ∧ z ≤ (2*R)^2 := by
  let t := 3*R/2
  let M := t • (1:Mat n)+E
  change ∀ z ∈ spectrum ℝ (Mᵀ*M), _
  intro z hz
  have he : Mᵀ*M-t^2 • (1:Mat n)=t • E + t • Eᵀ + Eᵀ*E := by
    simp only [M,transpose_add,transpose_smul,transpose_one,add_mul,mul_add,Matrix.smul_mul,
      Matrix.mul_smul,one_mul,mul_one,smul_smul,sq]
    abel
  have hz' : z-t^2 ∈ spectrum ℝ (Mᵀ*M-t^2 • (1:Mat n)) := by
    rw [spectrum.mem_iff,Algebra.algebraMap_eq_smul_one,sub_smul]
    rw [show z • (1:Mat n)-t^2 • 1-(Mᵀ*M-t^2 • 1)=z • 1-Mᵀ*M by abel]
    simpa only [spectrum.mem_iff,Algebra.algebraMap_eq_smul_one] using hz
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hnorm : ‖Eᵀ‖ = ‖E‖ := Matrix.l2_opNorm_conjTranspose E
  have herr : |z-t^2| ≤ t*‖E‖ + t*‖E‖ + ‖E‖*‖E‖ := calc
    |z-t^2| ≤ ‖Mᵀ*M-t^2 • (1:Mat n)‖ := spectrum.norm_le_norm_of_mem hz'
    _ = _ := congrArg norm he
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_mul_le _ _))
    _ = _ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,hnorm]
  have htE := mul_le_mul_of_nonneg_left hE ht
  have hEE := mul_self_le_mul_self (norm_nonneg E) hE
  obtain ⟨hneg,hpos⟩ := abs_le.mp herr
  dsimp [t] at *
  constructor <;> nlinarith only [hneg,hpos,htE,hEE,sq_pos_of_pos hr]

set_option maxHeartbeats 800000 in
private lemma window_norm {n : ℕ} [Nonempty (Fin n)] (M : Mat n) {R : ℝ} (hr : 0 ≤ R)
    (hM : ∀ z ∈ spectrum ℝ (Mᵀ*M), R^2 < z ∧ z ≤ (2*R)^2) : ‖M‖ ≤ 2*R := by
  let G := Mᴴ*M
  have hp : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  have hg : ‖G‖ ≤ (2*R)^2 := by
    calc ‖G‖ = ‖Unitary.conjStarAlgAut ℝ _ hp.1.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hp.1.eigenvalues))‖ :=
           congrArg norm hp.1.spectral_theorem
         _ = ‖hp.1.eigenvalues‖ := by
           simp only [Unitary.conjStarAlgAut_apply,← Unitary.coe_star,CStarRing.norm_mul_coe_unitary,
             CStarRing.norm_coe_unitary_mul,l2_opNorm_diagonal]
           rfl
         _ ≤ _ := by
           apply (pi_norm_le_iff_of_nonneg (sq_nonneg _)).mpr
           intro i
           rw [Real.norm_eq_abs,abs_of_nonneg (hp.eigenvalues_nonneg i)]
           apply (hM _ _).2
           exact hp.1.eigenvalues_mem_spectrum_real i
  change ‖Mᴴ*M‖ ≤ _ at hg
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hg
  exact le_of_sq_le_sq (by simpa only [sq] using hg) (by positivity)

end OMA.S_mo_339727

namespace OMA.S_mo_339727
open Matrix Finset
open scoped Matrix.Norms.L2Operator
variable {O : Type*} [CommRing O] {n : ℕ}

private noncomputable def repHom (b : Module.Basis (Fin n) ℤ O) : O →+* Mat n :=
  (Int.castRingHom ℝ).mapMatrix.comp (Algebra.leftMulMatrix b).toRingHom

private lemma regular_sum (b : Module.Basis (Fin n) ℤ O) (q : ℤ) (v : Fin n → ℤ) :
    regular b ((q:O) + b.equivFun.symm v) = (q:ℝ) • (1:Mat n) + ∑ i, (v i:ℝ) • regular b (b i) := by
  change repHom b _ = _
  rw [b.equivFun_symm_apply,map_add,map_intCast,map_sum]
  congr 1
  · change (q:Mat n)=_
    rw [Int.cast_smul_eq_zsmul,zsmul_eq_mul,mul_one]
  · apply sum_congr rfl
    intro i _
    rw [zsmul_eq_mul,map_mul,map_intCast,Int.cast_smul_eq_zsmul,zsmul_eq_mul]
    rfl

private noncomputable def unitVec (b : Module.Basis (Fin n) ℤ O) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => ((b.repr 1 j:ℤ):ℝ))

private lemma coord_bound (b : Module.Basis (Fin n) ℤ O) (x : O) (i : Fin n) :
    |((b.repr x i : ℤ):ℝ)| ≤ ‖regular b x‖ * ‖unitVec b‖ := by
  let w : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv _ ℝ).symm (regular b x *ᵥ unitVec b)
  have hw : w i = ((b.repr x i : ℤ):ℝ) := by
    have hi := congrFun (Algebra.leftMulMatrix_mulVec_repr b x (1:O)) i
    simp only [mul_one,Matrix.mulVec,dotProduct] at hi
    change (∑ j,((Algebra.leftMulMatrix b x i j:ℤ):ℝ)*((b.repr 1 j:ℤ):ℝ))=_
    exact_mod_cast hi
  rw [←hw,←Real.norm_eq_abs]
  exact (PiLp.norm_apply_le w i).trans ((regular b x).l2_opNorm_mulVec (unitVec b))
end OMA.S_mo_339727

namespace OMA.S_mo_339727
open Matrix Finset
open scoped Matrix.Norms.L2Operator
variable {O : Type*} [CommRing O] {n : ℕ} [Nonempty (Fin n)]

private lemma box_upper (b : Module.Basis (Fin n) ℤ O) (R : ℝ) (hr : 1 ≤ R) :
    (shell b R).Finite ∧ ((shell b R).ncard:ℝ) ≤ (4*‖unitVec b‖+3)^n*R^n := by
  classical
  let B := 2*R*‖unitVec b‖
  let m : ℕ := ⌈B⌉₊
  let J := Finset.Icc (-(m:ℤ)) (m:ℤ)
  let f (v : Fin n → J) := b.equivFun.symm (fun i => (v i:ℤ))
  have hf : Function.Injective f := by
    intro u v h
    have hh := b.equivFun.symm.injective h
    exact funext (fun i => Subtype.ext (congrFun hh i))
  have sub : shell b R ⊆ Set.range f := by
    intro x hx
    have hu := window_norm (regular b x) (by linarith : 0 ≤ R) hx
    have hb (i : Fin n) : b.repr x i ∈ J := by
      have h := ((coord_bound b x i).trans (mul_le_mul_of_nonneg_right hu (norm_nonneg _))).trans (Nat.le_ceil B)
      rw [abs_le] at h
      apply Finset.mem_Icc.mpr
      exact_mod_cast h
    refine ⟨fun i => ⟨_,hb i⟩,?_⟩
    exact b.equivFun.symm_apply_apply x
  have hfinite := Set.finite_range f
  refine ⟨hfinite.subset sub,?_⟩
  have hc := Set.ncard_le_ncard sub hfinite
  rw [Set.ncard_range_of_injective hf,Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe] at hc
  have hj : (J.card:ℝ)=2*(m:ℝ)+1 := by
    have hh := Int.card_Icc_of_le (a:=-(m:ℤ)) (b:=(m:ℤ)) (by omega)
    exact_mod_cast (show (J.card:ℤ)=2*(m:ℤ)+1 by dsimp [J]; omega)
  have hm : (m:ℝ) < B+1 := Nat.ceil_lt_add_one (by dsimp [B]; positivity)
  calc ((shell b R).ncard:ℝ) ≤ (J.card:ℝ)^n := by exact_mod_cast hc
       _ ≤ ((4*‖unitVec b‖+3)*R)^n := by
         apply pow_le_pow_left₀ (by positivity)
         rw [hj]
         dsimp [B] at hm
         nlinarith only [hr,hm]
       _ = _ := mul_pow _ _ _

private noncomputable def basisSize (b : Module.Basis (Fin n) ℤ O) : ℝ :=
  1 + ∑ i,‖regular b (b i)‖
omit [Nonempty (Fin n)] in
private lemma size_pos (b : Module.Basis (Fin n) ℤ O) : 0 < basisSize b := by
  unfold basisSize
  positivity

private lemma box_lower (b : Module.Basis (Fin n) ℤ O) (R : ℝ) (hr : 32 ≤ R) :
    (32*basisSize b)⁻¹^n*R^n ≤ ((shell b R).ncard:ℝ) := by
  classical
  let K := basisSize b
  have hk : 0 < K := size_pos b
  let t := 3*R/2
  let q := ⌊t⌋
  let B := R/(32*K)
  let m : ℕ := ⌊B⌋₊+1
  let f (v : Fin n → Fin m) : O := (q:O)+b.equivFun.symm (fun i => ((v i).val:ℤ))
  have hf : Function.Injective f := by
    intro u v h
    change (q:O)+_= (q:O)+_ at h
    have hh := b.equivFun.symm.injective (add_left_cancel h)
    funext i
    exact Fin.ext (by exact_mod_cast congrFun hh i)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpert (v : Fin n → Fin m) : ‖regular b (f v) - t • (1:Mat n)‖ ≤ R/8 := by
    rw [show f v=(q:O)+b.equivFun.symm (fun i => ((v i).val:ℤ)) from rfl,regular_sum]
    let S := ∑ i, ((v i).val:ℝ) • regular b (b i)
    have hs : ‖S‖ ≤ B*(∑ i,‖regular b (b i)‖) := calc
      ‖S‖ ≤ ∑ i,‖((v i).val:ℝ) • regular b (b i)‖ := norm_sum_le _ _
      _ ≤ _ := by
        rw [Finset.mul_sum]
        apply sum_le_sum
        intro i _
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have hv : (v i).val ≤ ⌊B⌋₊ := by have hi := (v i).isLt; dsimp [m] at hi; omega
        exact (Nat.cast_le.mpr hv).trans (Nat.floor_le hB)
    have he : (q:ℝ) • (1:Mat n)+S-t • 1=((q:ℝ)-t) • 1+S := by rw [sub_smul]; abel
    change ‖(q:ℝ) • (1:Mat n)+S-t • 1‖ ≤ _
    rw [he]
    apply (norm_add_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs,norm_one,mul_one]
    have hq : |(q:ℝ)-t| ≤ 1 := abs_le.mpr ⟨by linarith [Int.lt_floor_add_one t],by linarith [Int.floor_le t]⟩
    have hBK : B*K=R/32 := by dsimp [B]; field_simp
    dsimp [K,basisSize] at hBK
    nlinarith only [hs,hq,hBK,hr,hB]
  have sub : Set.range f ⊆ shell b R := by
    rintro _ ⟨v,rfl⟩
    have h := window_near_scalar (regular b (f v)-t • 1) (by linarith : 0 < R) (hpert v)
    change ∀ z ∈ spectrum ℝ ((t • 1+(regular b (f v)-t • 1))ᵀ*(t • 1+(regular b (f v)-t • 1))), _ at h
    change ∀ z ∈ spectrum ℝ ((regular b (f v))ᵀ*regular b (f v)), _
    simpa only [←add_sub_assoc,add_sub_cancel_left] using h
  have hc := Set.ncard_le_ncard sub (box_upper b R (by linarith)).1
  rw [Set.ncard_range_of_injective hf,Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin] at hc
  have hBm : B ≤ (m:ℝ) := by
    simpa [m] using (Nat.lt_floor_add_one B).le
  calc (32*basisSize b)⁻¹^n*R^n = B^n := by rw [←mul_pow]; congr 1; exact (div_eq_inv_mul _ _).symm
       _ ≤ (m:ℝ)^n := pow_le_pow_left₀ hB hBm _
       _ ≤ _ := by exact_mod_cast hc

private theorem solve (O : Type*) [CommRing O] (n : ℕ) (b : Module.Basis (Fin n) ℤ O) (hn : 0 < n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ R : ℝ in Filter.atTop, (shell b R).Finite ∧
      c*R^n ≤ ((shell b R).ncard:ℝ) ∧ ((shell b R).ncard:ℝ) ≤ C*R^n := by
  let _ : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hk := size_pos b
  refine ⟨(32*basisSize b)⁻¹^n,(4*‖unitVec b‖+3)^n,by positivity,by positivity,?_⟩
  filter_upwards [Filter.eventually_ge_atTop (32:ℝ)] with R hR
  have hh := box_upper b R (by linarith)
  exact ⟨hh.1,box_lower b R hR,hh.2⟩
end OMA.S_mo_339727

open OMA.S_mo_339727 in
theorem OMA.solution : type_of% @OMA.S_mo_339727.main := solve
