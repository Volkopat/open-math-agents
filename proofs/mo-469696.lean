import OMAStatements.S_mo_469696

namespace OMA.S_mo_469696
open Matrix Finset
open scoped ComplexOrder
private lemma symK (a b : ℝ) : star (K a b)=K b a := by
  simp [K]
  ring
private lemma kernel_herm {ι : Type} (x : ι → ℝ) : (gram x).IsHermitian := by
  ext i j
  exact symK _ _
private lemma dne (a b : ℝ) : (1-Complex.I*((b:ℂ)-a))≠0 := by
  intro he
  have hr := congrArg Complex.re he
  simp at hr
private lemma project (a b t : ℝ) :
    K a b - K a t * star (K b t)=(1-K a t)*K a b*star (1-K b t) := by
  rw [star_sub, star_one, symK]
  unfold K
  field_simp [dne]
  ring
private noncomputable def vcol {n : ℕ} (t : ℝ) (x : Fin n → ℝ) : Matrix (Fin n) Unit ℂ :=
  fun i _ => K (x i) t
private noncomputable def disc {n : ℕ} (t : ℝ) (x : Fin n → ℝ) : Sq (Fin n) :=
  diagonal (fun i => 1-K (x i) t)
private lemma border_eq {n : ℕ} (t : ℝ) (x : Fin n → ℝ) :
    bordered t x=fromBlocks 1 (vcol t x)ᴴ (vcol t x) (gram x) := by
  ext (i|i) (j|j)
  · simp [bordered,gram,fromBlocks,K]
  · simp [bordered,gram,fromBlocks,vcol,conjTranspose_apply,symK]
  · rfl
  · rfl
private lemma schur_eq {n : ℕ} (t : ℝ) (x : Fin n → ℝ) :
    gram x-vcol t x*(vcol t x)ᴴ=disc t x*gram x*(disc t x)ᴴ := by
  ext i j
  simp only [disc,diagonal_conjTranspose,mul_diagonal,diagonal_mul]
  simpa [gram,vcol,Matrix.mul_apply,conjTranspose_apply] using project (x i) (x j) t
private lemma border_psd {n : ℕ} (t : ℝ) (x : Fin n → ℝ) (h : (gram x).PosSemidef) :
    (bordered t x).PosSemidef := by
  let D := disc t x
  let V := vcol t x
  let R : Sq (Unit ⊕ Fin n) := fromBlocks 1 0 V D
  have hdiag : (fromBlocks (1:Sq Unit) 0 0 (gram x)).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · simp [IsHermitian,fromBlocks_conjTranspose,h.1.eq]
    · intro y
      simp [fromBlocks_mulVec,dotProduct,Fintype.sum_sum_type]
      exact add_nonneg (star_mul_self_nonneg _) (h.dotProduct_mulVec_nonneg _)
  have hh := hdiag.mul_mul_conjTranspose_same R
  have he := schur_eq t x
  have hz : V*Vᴴ + D*gram x*Dᴴ=gram x := by
    change _=gram x
    dsimp [D,V]
    rw [← he]
    abel
  simpa [R,fromBlocks_conjTranspose,fromBlocks_multiply,hz,border_eq,V] using hh

private def headEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n+1) :=
  { toFun := Sum.elim (fun _ => 0) Fin.succ
    invFun := Fin.cases (Sum.inl ()) Sum.inr
    left_inv := by rintro (i|i) <;> simp
    right_inv := by intro i; induction i using Fin.cases <;> simp }

private lemma gram_psd {n : ℕ} (x : Fin n → ℝ) : (gram x).PosSemidef := by
  induction n with
  | zero => exact Subsingleton.elim (gram x) 0 ▸ Matrix.PosSemidef.zero
  | succ n ih =>
    let w := fun j : Fin n => x j.succ
    have hs := (border_psd (x 0) w (ih w)).submatrix (headEquiv n).symm
    have hh : x = (Sum.elim (fun _ : Unit => x 0) w) ∘ (headEquiv n).symm := by
      funext i
      induction i using Fin.cases <;> rfl
    rw [hh]
    exact hs

private lemma ratio_norm (a t : ℝ) : Complex.normSq (1-K a t)=(a-t)^2/(1+(a-t)^2) := by
  let q : ℂ := 1-Complex.I*((t:ℂ)-a)
  have h : 1-K a t = (q-1)/q := by
    change 1-q⁻¹=(q-1)/q
    field_simp [show q≠0 from dne a t]
  rw [h,Complex.normSq_div]
  simp [q,Complex.normSq_apply]
  ring

open Unitary

private noncomputable def aff {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ℝ)
    (A : Sq ι) : Sq ι := (a:ℂ) • 1 + (b:ℂ) • A

private lemma aff_spec {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ℝ)
    {A : Sq ι} (h : A.IsHermitian) : aff a b A =
    conjStarAlgAut ℂ _ h.eigenvectorUnitary (diagonal fun i => ((a+b*h.eigenvalues i:ℝ):ℂ)) := by
  let U := conjStarAlgAut ℂ _ h.eigenvectorUnitary
  have he : (diagonal fun i => ((a+b*h.eigenvalues i:ℝ):ℂ)) =
      (a:ℂ) • 1 + (b:ℂ) • diagonal (RCLike.ofReal ∘ h.eigenvalues) := by
    ext i j
    by_cases hj : i=j
    · subst j
      simp
    · simp [diagonal,one_apply,hj]
  rw [he]
  change _ = U _
  rw [map_add,map_smul,map_smul,map_one]
  exact congrArg (fun M : Sq ι => (a:ℂ) • 1 + (b:ℂ) • M) h.spectral_theorem

private lemma aff_pos {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ℝ)
    {A : Sq ι} (h : A.IsHermitian) :
    (aff a b A).PosDef ↔ ∀ i, 0 < a+b*h.eigenvalues i := by
  rw [aff_spec a b h]
  simp [isUnit_coe.posDef_star_right_conjugate_iff, -Complex.ofReal_mul, -Complex.ofReal_add]

private lemma aff_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ℝ)
    {A : Sq ι} (h : A.IsHermitian) :
    (aff a b A).PosSemidef ↔ ∀ i, 0 ≤ a+b*h.eigenvalues i := by
  rw [aff_spec a b h]
  simp [isUnit_coe.posSemidef_star_right_conjugate_iff,posSemidef_diagonal_iff, -Complex.ofReal_mul, -Complex.ofReal_add]

private lemma aff_det {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ℝ)
    {A : Sq ι} (h : A.IsHermitian) :
    (aff a b A).det = ((∏ i, (a+b*h.eigenvalues i)):ℝ) := by
  rw [aff_spec a b h,conjStarAlgAut_apply,det_mul_comm,←mul_assoc]
  simp



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

private lemma eigen_mono {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
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


private noncomputable def schur {n : ℕ} (t : ℝ) (x : Fin n → ℝ) : Sq (Fin n) :=
  gram x-vcol t x*(vcol t x)ᴴ

private lemma schur_psd {n : ℕ} (t : ℝ) (x : Fin n → ℝ) : (schur t x).PosSemidef := by
  rw [schur,schur_eq]
  exact (gram_psd x).mul_mul_conjTranspose_same _

private lemma discs_order {n : ℕ} (x : Fin n → ℝ) (s t : ℝ)
    (h : ∀ i, |x i-s| ≤ |x i-t|) :
    ((disc t x)ᴴ*disc t x-(disc s x)ᴴ*disc s x).PosSemidef := by
  have he (u : ℝ) : (disc u x)ᴴ*disc u x =
      diagonal (fun i => (Complex.normSq (1-K (x i) u):ℂ)) := by
    simp [disc,diagonal_mul_diagonal, Complex.normSq_eq_conj_mul_self]
  rw [he,he,diagonal_sub]
  apply posSemidef_diagonal_iff.mpr
  intro i
  simp only [sub_nonneg]
  norm_cast
  rw [ratio_norm,ratio_norm]
  have hh := (sq_le_sq).mpr (h i)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  linarith

private lemma schur_eigen_mono {n : ℕ} (x : Fin n → ℝ) (s t : ℝ)
    (h : ∀ i, |x i-s| ≤ |x i-t|) (i : Fin n) :
    (schur_psd s x).1.eigenvalues i ≤ (schur_psd t x).1.eigenvalues i := by
  open scoped MatrixOrder in
    obtain ⟨W,hW⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (gram_psd x).nonneg
  let T := fun u => disc u x * Wᴴ
  have hT (u : ℝ) : schur u x = T u*(T u)ᴴ := by
    rw [schur,schur_eq,hW]
    simp [T,mul_assoc,star_eq_conjTranspose]
  have he (u : ℝ) : (schur_psd u x).1.eigenvalues =
      (isHermitian_conjTranspose_mul_self (T u)).eigenvalues := by
    apply (IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).2
    rw [hT,charpoly_mul_comm]
  rw [he,he]
  apply eigen_mono
  have hm := (discs_order x s t h).mul_mul_conjTranspose_same W
  simpa [T,mul_sub,sub_mul,mul_assoc] using hm

private lemma block_aff {n : ℕ} (a b t : ℝ) (x : Fin n → ℝ) :
    aff a b (bordered t x) = fromBlocks (((a+b:ℝ):ℂ) • (1:Sq Unit))
      ((b:ℂ) • (vcol t x)ᴴ) ((b:ℂ) • vcol t x) (aff a b (gram x)) := by
  rw [border_eq]
  ext (i|i) (j|j) <;> simp [aff,fromBlocks,one_apply,add_smul]

private lemma aff_corner {n : ℕ} (a b t : ℝ) (x : Fin n → ℝ)
    (h : (aff a b (bordered t x)).PosDef) : (aff a b (gram x)).PosDef := by
  rw [block_aff] at h
  exact h.submatrix Sum.inr_injective

private lemma det_low {n : ℕ} (a t : ℝ) (x : Fin n → ℝ)
    (h : IsUnit (aff a 1 (gram x))) : (aff a 1 (bordered t x)).det =
    (aff a 1 (schur t x)).det + a*(aff a 1 (gram x)).det := by
  let H := aff a 1 (gram x)
  let V := vcol t x
  let := h.invertible
  have hs : aff a 1 (schur t x) = H-V*Vᴴ := by simp [H,V,schur,aff]; abel
  rw [block_aff,hs,← det_fromBlocks_one₁₁]
  change _= (fromBlocks (1:Sq Unit) Vᴴ V H).det + (a:ℂ)*H.det
  simp only [Complex.ofReal_one,one_smul,Complex.ofReal_add]
  rw [det_fromBlocks₂₂,det_fromBlocks₂₂]
  simp [det_unique, H,V]
  ring

private lemma aff_neg {ι : Type} [Fintype ι] [DecidableEq ι] (a : ℝ) (A : Sq ι) :
    aff a (-1) A = -aff (-a) 1 A := by
  simp [aff,add_comm]

private lemma det_high {n : ℕ} (a t : ℝ) (x : Fin n → ℝ)
    (h : IsUnit (aff a (-1) (gram x))) : (aff a (-1) (bordered t x)).det =
    -(aff a (-1) (schur t x)).det + a*(aff a (-1) (gram x)).det := by
  simp only [aff_neg, IsUnit.neg_iff] at h
  simp only [aff_neg,det_neg,Fintype.card_sum,Fintype.card_unit,Fintype.card_fin,
    det_low (-a) t x h,Complex.ofReal_neg]
  rw [pow_add]
  ring

private lemma low_schur {n : ℕ} (a t : ℝ) (x : Fin n → ℝ) (ha : a≤0)
    (h : (aff a 1 (bordered t x)).PosSemidef) : (aff a 1 (schur t x)).PosSemidef := by
  let V := vcol t x
  let H := aff a 1 (gram x)
  let T : Sq (Unit ⊕ Fin n) := fromBlocks 1 0 (-V) 1
  have hpad : (fromBlocks ((-a:ℂ) • (1:Sq Unit)) 0 0 (0:Sq (Fin n))).PosSemidef := by
    have he : fromBlocks ((-a:ℂ) • (1:Sq Unit)) 0 0 (0:Sq (Fin n)) =
        diagonal (Sum.elim (fun _ : Unit => (-a:ℂ)) (fun _ : Fin n => 0)) := by
      ext (i|i) (j|j) <;> simp [fromBlocks,diagonal,one_apply]
    rw [he,posSemidef_diagonal_iff]
    rintro (i|i)
    · simpa using (show (a:ℂ) ≤ 0 by exact_mod_cast ha)
    · simp
  have hw : (fromBlocks (1:Sq Unit) Vᴴ V H).PosSemidef := by
    convert h.add hpad using 1
    rw [block_aff,fromBlocks_add]
    simp [H,V,add_smul,add_assoc,add_comm]
  have hm := (hw.mul_mul_conjTranspose_same T).submatrix (Sum.inr : Fin n → Unit ⊕ Fin n)
  change (aff a 1 (schur t x)).PosSemidef
  convert hm using 1
  simp [T,fromBlocks_conjTranspose,fromBlocks_multiply,H,V,aff,schur]
  ext i j
  simp [submatrix_apply]
  abel

private lemma lower {n : ℕ} (x : Fin n → ℝ) (s t : ℝ) (h : ∀ i, |x i-s| ≤ |x i-t|)
    (i : Unit ⊕ Fin n) : ∃ j, eigenvalue s x j ≤ eigenvalue t x i := by
  let z := eigenvalue t x i
  have ht := border_psd t x (gram_psd x)
  have hs := border_psd s x (gram_psd x)
  have hz : 0≤z := ht.eigenvalues_nonneg i
  by_contra! hn
  have hp : (aff (-z) 1 (bordered s x)).PosDef := by
    apply (aff_pos _ _ hs.1).2
    intro j
    have := hn j
    change z < hs.1.eigenvalues j at this
    linarith
  have hu := (aff_corner _ _ _ _ hp).isUnit
  have hc := (aff_nonneg _ _ (schur_psd s x).1).1 (low_schur (-z) s x (by linarith) hp.posSemidef)
  have hle : (aff (-z) 1 (schur s x)).det ≤ (aff (-z) 1 (schur t x)).det := by
    rw [aff_det _ _ (schur_psd s x).1, aff_det _ _ (schur_psd t x).1]
    exact_mod_cast Finset.prod_le_prod (fun j _ => hc j)
      (fun j _ => add_le_add_right (mul_le_mul_of_nonneg_left (schur_eigen_mono x s t h j) zero_le_one) _)
  have hzero : (aff (-z) 1 (bordered t x)).det = 0 := by
    rw [aff_det _ _ ht.1, Finset.prod_eq_zero (i := i) (by simp) (by change -z+1*z=0; ring)]
    simp
  have hnz := hp.det_pos
  rw [det_low _ _ _ hu] at hzero hnz
  exact (not_lt_of_ge ((add_le_add_left hle _).trans_eq hzero)) hnz

private lemma upper {n : ℕ} (x : Fin n → ℝ) (s t : ℝ) (h : ∀ i, |x i-s| ≤ |x i-t|)
    (i : Unit ⊕ Fin n) : ∃ j, eigenvalue t x i ≤ eigenvalue s x j := by
  let z := eigenvalue t x i
  have ht := border_psd t x (gram_psd x)
  have hs := border_psd s x (gram_psd x)
  by_contra! hn
  have hp : (aff z (-1) (bordered s x)).PosDef := by
    apply (aff_pos _ _ hs.1).2
    intro j
    have := hn j
    change hs.1.eigenvalues j < z at this
    linarith
  have hcorner := aff_corner _ _ _ _ hp
  have hu := hcorner.isUnit
  have hb : (aff z (-1) (schur t x)).PosSemidef := by
    convert hcorner.posSemidef.add (posSemidef_self_mul_conjTranspose (vcol t x)) using 1
    simp [aff,schur]
    abel
  have hc := (aff_nonneg _ _ (schur_psd t x).1).1 hb
  have hle : (aff z (-1) (schur t x)).det ≤ (aff z (-1) (schur s x)).det := by
    rw [aff_det _ _ (schur_psd t x).1, aff_det _ _ (schur_psd s x).1]
    exact_mod_cast Finset.prod_le_prod (fun j _ => hc j)
      (fun j _ => add_le_add_right (mul_le_mul_of_nonpos_left (schur_eigen_mono x s t h j) (by norm_num : (-1:ℝ)≤0)) _)
  have hzero : (aff z (-1) (bordered t x)).det = 0 := by
    rw [aff_det _ _ ht.1, Finset.prod_eq_zero (i := i) (by simp) (by change z+-1*z=0; ring)]
    simp
  have hnz := hp.det_pos
  rw [det_high _ _ _ hu] at hzero hnz
  exact (not_lt_of_ge ((add_le_add_left (neg_le_neg hle) _).trans_eq hzero)) hnz

private lemma kernel_norm (t y : ℝ) : K t y * K y t = ((1+(y-t)^2)⁻¹:ℝ) := by
  rw [← symK t y,mul_comm]
  change (starRingEnd ℂ) (K t y) * K t y = _
  rw [← Complex.normSq_eq_conj_mul_self]
  norm_cast
  simp [K,Complex.normSq_apply]
  ring

private lemma two_det (z t y : ℝ) : (aff (-z) 1 (bordered t (fun _ : Fin 1 => y))).det =
    (((1-z)^2-(1+(y-t)^2)⁻¹:ℝ):ℂ) := by
  rw [← det_submatrix_equiv_self (headEquiv 1).symm, det_fin_two]
  have h0 : (headEquiv 1).symm 0 = Sum.inl () := rfl
  have h1 : (headEquiv 1).symm 1 = Sum.inr 0 := rfl
  have hK (a : ℝ) : K a a = 1 := by simp [K]
  simp [submatrix_apply,h0,h1,aff,bordered,gram,one_apply,hK,kernel_norm]
  ring

private lemma negative_example : ∃ i : Unit ⊕ Fin 1, ∀ j : Unit ⊕ Fin 1,
    eigenvalue 0 (fun _ => 1) i < eigenvalue (-1) (fun _ => 1) j := by
  let x : Fin 1 → ℝ := fun _ => 1
  have hs := border_psd 0 x (gram_psd x)
  have ht := border_psd (-1) x (gram_psd x)
  have hl : ∃ i, eigenvalue 0 x i < 1/2 := by
    by_contra! hn
    have hp : (aff (-(1/2)) 1 (bordered 0 x)).PosSemidef := by
      apply (aff_nonneg _ _ hs.1).2
      intro j
      have := hn j
      change 1/2 ≤ hs.1.eigenvalues j at this
      linarith
    have := (RCLike.nonneg_iff.mp hp.det_nonneg).1
    rw [show (aff (-(1/2)) 1 (bordered 0 x)).det = _ from two_det (1/2) 0 1] at this
    norm_num at this

  obtain ⟨i,hi⟩ := hl
  refine ⟨i, fun j => hi.trans ?_⟩
  let z := eigenvalue (-1) x j
  have hz : (aff (-z) 1 (bordered (-1) x)).det = 0 := by
    rw [aff_det _ _ ht.1,Finset.prod_eq_zero (i := j) (by simp) (by change -z+1*z=0; ring)]
    simp
  rw [show (aff (-z) 1 (bordered (-1) x)).det = _ from two_det z (-1) 1] at hz
  norm_cast at hz
  norm_num at hz
  change 1/2 < z
  by_contra! hn
  nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show (0:ℝ) ≤ 3/2-z by linarith)]

private lemma bounds {n : ℕ} (x : Fin n → ℝ) (s t : ℝ) (h : ∀ i, |x i-s| ≤ |x i-t|) :
    leastEigen s x ≤ leastEigen t x ∧ greatestEigen t x ≤ greatestEigen s x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (eigenvalue t x)
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (eigenvalue t x)
  obtain ⟨j, hj⟩ := lower x s t h i
  obtain ⟨l, hl⟩ := upper x s t h k
  exact ⟨(Finset.inf'_le _ (Finset.mem_univ j)).trans (hj.trans_eq hi.symm),
    hk.le.trans (hl.trans (Finset.le_sup' _ (Finset.mem_univ l)))⟩

private lemma failure : leastEigen 0 (fun _ : Fin 1 => 1) <
    leastEigen (-1) (fun _ : Fin 1 => 1) := by
  obtain ⟨i,hi⟩ := negative_example
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (eigenvalue (-1) (fun _ : Fin 1 => 1))
  exact (Finset.inf'_le _ (Finset.mem_univ i)).trans_lt ((hi j).trans_eq hj.symm)


theorem answer :
    (∀ (n : ℕ) (x : Fin n → ℝ) (s t : ℝ), (∀ j, |x j-s| ≤ |x j-t|) →
      leastEigen s x ≤ leastEigen t x ∧ greatestEigen t x ≤ greatestEigen s x) ∧
    (∀ (n : ℕ) (x : Fin n → ℝ) (t ε : ℝ), 0 ≤ ε → (∀ j, t+ε ≤ x j) →
      leastEigen (t+ε) x ≤ leastEigen t x) ∧
    leastEigen 0 (fun _ : Fin 1 => 1) < leastEigen (-1) (fun _ : Fin 1 => 1) := by
  refine ⟨fun n x s t h => bounds x s t h, ?_, failure⟩
  intro n x t ε he hx
  apply (bounds x (t+ε) t ?_).1
  intro j
  rw [abs_of_nonneg (by linarith [hx j] : 0 ≤ x j-(t+ε)),
    abs_of_nonneg (by linarith [hx j] : 0 ≤ x j-t)]
  linarith

end OMA.S_mo_469696
open OMA.S_mo_469696 in
theorem OMA.solution : type_of% @OMA.S_mo_469696.main := answer
